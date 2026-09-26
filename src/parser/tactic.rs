//! The tactic grammar.
//!
//! Per the chosen scope, individual tactics are *not* interpreted: a tactic is
//! its leading token plus a bracket-balanced run of arguments. What the parser
//! does model is the structure that governs control flow and, crucially,
//! layout — sequencing, focus dots, `<;>`, `first | …`, and parenthesised
//! blocks.
//!
//! Getting layout right is what lets a nested `by` block end correctly:
//!
//! ```lean
//! theorem t : p := by
//!   have h : q := by
//!     simp
//!   exact h      -- dedent ends the inner block, not the outer one
//! ```
//!
//! Recognising individual tactics is the natural next step; see `TACTIC` below
//! for where a real tactic rule would slot in.

use super::Grammar;
use super::support::*;
use crate::kind::SyntaxKind::{self, *};
use crate::syntax::Frag;
use chumsky::prelude::*;

/// Tokens that end a tactic's argument run at bracket depth zero.
fn ends_tactic(kind: SyntaxKind) -> bool {
    matches!(kind, SEMICOLON | SEQ_FOCUS)
}

/// Ends the pattern part of a `with` alternative.
fn ends_alt_pattern(kind: SyntaxKind) -> bool {
    kind == FAT_ARROW
}

/// Tokens that may not begin a tactic.
///
/// Without this the generic rule would happily swallow the `)` that closes a
/// bracketed block, or the `|` separating `first` alternatives.
fn cannot_start_tactic(kind: SyntaxKind) -> bool {
    is_closer(kind)
        || matches!(
            kind,
            SEMICOLON | SEQ_FOCUS | PIPE | COMMA | FAT_ARROW | COLON_EQ
        )
}

/// Guards the generic tactic rule against tokens that cannot start a tactic.
fn tactic_head<'a>() -> impl Parser<'a, In<'a>, Frag, Extra<'a>> + Clone {
    any_tok_if(|k| !cannot_start_tactic(k))
}

/// A `by` block's tactic sequence.
pub fn tactic_seq<'a>(g: &Grammar<'a>) -> BoxedP<'a, Frag> {
    let seq = g.tactic_seq.clone();

    // An uninterpreted tactic: one leading token, then a balanced argument run
    // that stops at a separator or at a dedent.
    // `induction n with | zero => … | succ k ih => …` — the alternatives are
    // structured (each body is a real tactic sequence) even though the tactic
    // introducing them is not.
    let alt = node(
        MATCH_ALT,
        group((
            tok(PIPE),
            balanced_run(PATTERNS, ends_alt_pattern, true),
            tok(FAT_ARROW),
            seq.clone(),
        )),
    );

    let generic = node(
        TACTIC,
        group((
            tactic_head(),
            balanced_run(TACTIC_ARGS, ends_tactic, true),
            layout_block(MATCH_ALTS, alt, &[], false).or_not(),
        )),
    );

    let base = choice((
        // `· tac` / `• tac` — focus on the first goal.
        node(TACTIC_FOCUS, group((tok_in(&[CDOT, BULLET]), seq.clone()))),
        // `(tac; tac)` — an explicit block.
        node(
            TACTIC_SEQ_BRACKETED,
            group((tok(L_PAREN), seq.clone(), tok(R_PAREN))),
        ),
        // `first | tac | tac`
        node(
            TACTIC_ALT,
            group((
                tok(KW_FIRST),
                group((tok(PIPE), seq.clone()))
                    .repeated()
                    .at_least(1)
                    .collect::<Vec<_>>(),
            )),
        ),
        generic,
    ))
    .boxed();

    // `tac <;> tac` applies the right tactic to every goal the left produced.
    let item = base
        .clone()
        .then(
            group((tok(SEQ_FOCUS), base.clone()))
                .repeated()
                .collect::<Vec<_>>(),
        )
        .map(|(first, rest)| {
            if rest.is_empty() {
                first
            } else {
                let mut kids = vec![first];
                rest.push_kids(&mut kids);
                Frag::Node(TACTIC_COMBINATOR, kids)
            }
        });

    layout_block(TACTIC_SEQ, item, &[SEMICOLON], true).boxed()
}
