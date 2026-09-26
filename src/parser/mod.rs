//! The Lean 4 parser.
//!
//! [`parse`] is the entry point. It always returns a tree: unparsable regions
//! become `ERROR` nodes holding their tokens, so a file with a syntax error
//! still round-trips and still yields usable structure for everything around
//! the error.

pub mod command;
pub mod support;
pub mod tactic;
pub mod term;

use crate::kind::SyntaxKind::{ERROR, SOURCE_FILE};
use crate::lexer::{RawToken, lex};
use crate::syntax::{
    Frag, Parse, ParseError, SigToken, materialize, significant, token_range_to_text_range,
};
use chumsky::input::InputRef;
use chumsky::prelude::*;
use support::{Extra, In, Rec};

/// The mutually recursive parsers. Handles are `Rc`-backed, so they can be
/// cloned into the rules that reference them and defined afterwards.
#[derive(Clone)]
pub struct Grammar<'a> {
    /// Any term.
    pub term: Rec<'a>,
    /// A `by` block's tactic sequence.
    pub tactic_seq: Rec<'a>,
    /// A `do` block's statement sequence.
    pub do_seq: Rec<'a>,
    /// A single top-level command.
    pub command: Rec<'a>,
}

impl<'a> Grammar<'a> {
    /// Declares the recursive parsers and ties the knot.
    pub fn build() -> Grammar<'a> {
        let mut g = Grammar {
            term: Recursive::declare(),
            tactic_seq: Recursive::declare(),
            do_seq: Recursive::declare(),
            command: Recursive::declare(),
        };
        // Clones share the same cell, so rules built from `handles` see the
        // definitions installed below.
        let handles = g.clone();
        g.term.define(term::term(&handles));
        g.tactic_seq.define(tactic::tactic_seq(&handles));
        g.do_seq.define(term::do_seq(&handles));
        g.command.define(command::command(&handles));
        g
    }
}

/// Parses a whole file as a sequence of commands, recovering from errors.
///
/// Each command establishes its own layout position, which is what stops an
/// application or a tactic block from running past the end of the command.
fn file<'a>(g: &Grammar<'a>) -> impl Parser<'a, In<'a>, Vec<Frag>, Extra<'a>> + use<'a> {
    let command = g.command.clone();
    custom(move |inp: &mut InputRef<'a, '_, In<'a>, Extra<'a>>| {
        let mut out = Vec::new();
        while let Some(first) = inp.peek() {
            let base = first.col;
            let before = *inp.cursor().inner();
            let checkpoint = inp.save();

            match inp.parse(command.clone().with_ctx(base)) {
                // A successful parse that consumed nothing would loop forever;
                // treat it as a failure so recovery makes progress.
                Ok(frag) if *inp.cursor().inner() > before => out.push(frag),
                Ok(_) => {
                    inp.rewind(checkpoint);
                    out.push(recover(inp, base));
                }
                Err(err) => {
                    inp.rewind(checkpoint);
                    inp.emit(err);
                    out.push(recover(inp, base));
                }
            }
        }
        Ok(out)
    })
}

/// Consumes tokens up to the next plausible command start, wrapping them in an
/// `ERROR` node. Always consumes at least one token.
fn recover<'a>(inp: &mut InputRef<'a, '_, In<'a>, Extra<'a>>, base: u32) -> Frag {
    let mut kids = Vec::new();
    let idx = *inp.cursor().inner();
    inp.skip();
    kids.push(Frag::Token(idx));
    while let Some(t) = inp.peek() {
        // A column-0 token starts new top-level syntax even when its kind is
        // not a recognised command keyword, which is what keeps one failed
        // declaration from swallowing the ones after it.
        if t.col <= base && (command::is_command_start(t.kind) || t.col == 0) {
            break;
        }
        let idx = *inp.cursor().inner();
        inp.skip();
        kids.push(Frag::Token(idx));
    }
    Frag::Node(ERROR, kids)
}

/// Parses Lean 4 source into a lossless syntax tree.
///
/// The returned [`Parse`] always contains a tree whose text is exactly `src`,
/// whether or not parsing succeeded.
pub fn parse(src: &str) -> Parse {
    let raws = lex(src);
    let sigs = significant(&raws);
    parse_tokens(&raws, &sigs)
}

fn parse_tokens<'a>(raws: &'a [RawToken<'a>], sigs: &'a [SigToken<'a>]) -> Parse {
    let grammar = Grammar::build();
    let parser = file(&grammar);
    let (out, errs) = parser.parse(sigs).into_output_errors();

    let errors = errs
        .into_iter()
        .map(|err| {
            let span = *err.span();
            ParseError {
                message: err.to_string(),
                range: token_range_to_text_range(sigs, raws, span.start, span.end),
            }
        })
        .collect();

    let frags = out.unwrap_or_default();
    Parse::new(materialize(SOURCE_FILE, &frags, raws, sigs), errors)
}
