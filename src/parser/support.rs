//! Building blocks shared by the term, command and tactic grammars.
//!
//! Two things are worth knowing before reading the grammar modules:
//!
//! * Because the parser input is `&[SigToken]`, chumsky's cursor *is* a token
//!   index, so `MapExtra::span().start` gives the index a token parser just
//!   consumed. That is how [`tok`] can produce a [`Frag::Token`].
//! * The parser context (`Extra`'s third parameter) carries one `u32`: the
//!   current indentation threshold. Lean's `colGt` means "this token must be
//!   indented past the enclosing syntactic position", and that is exactly what
//!   [`col_gt`] checks against the context. Blocks install a new threshold with
//!   `with_ctx`.

use crate::kind::SyntaxKind;
use crate::syntax::{Frag, SigToken};
use chumsky::error::Rich;
use chumsky::extra;
use chumsky::input::{InputRef, MapExtra};
use chumsky::prelude::*;
use chumsky::recursive::Indirect;

/// The parser input: significant tokens only.
pub type In<'a> = &'a [SigToken<'a>];

/// Error type, unit state, and a `u32` context holding the indentation
/// threshold for the enclosing block.
pub type Extra<'a> = extra::Full<Rich<'a, SigToken<'a>>, (), u32>;

/// A forward-declared parser, for the mutual recursion between terms, tactics
/// and commands.
pub type Rec<'a> = Recursive<Indirect<'a, 'a, In<'a>, Frag, Extra<'a>>>;

/// A type-erased parser producing `O`.
pub type BoxedP<'a, O> = chumsky::Boxed<'a, 'a, In<'a>, O, Extra<'a>>;

/// Anything that can contribute children to a node.
///
/// This exists so grammar rules can be written as `group((a, opt_b, many_c))`
/// and wrapped with [`node`] without hand-flattening the tuple.
pub trait IntoKids {
    /// Appends this value's fragments to `out`.
    fn push_kids(self, out: &mut Vec<Frag>);
}

impl IntoKids for Frag {
    fn push_kids(self, out: &mut Vec<Frag>) {
        out.push(self);
    }
}

impl IntoKids for () {
    fn push_kids(self, _: &mut Vec<Frag>) {}
}

impl<T: IntoKids> IntoKids for Option<T> {
    fn push_kids(self, out: &mut Vec<Frag>) {
        if let Some(v) = self {
            v.push_kids(out);
        }
    }
}

impl<T: IntoKids> IntoKids for Vec<T> {
    fn push_kids(self, out: &mut Vec<Frag>) {
        for v in self {
            v.push_kids(out);
        }
    }
}

impl<T: IntoKids> IntoKids for Box<T> {
    fn push_kids(self, out: &mut Vec<Frag>) {
        (*self).push_kids(out);
    }
}

/// Implements [`IntoKids`] for tuples, so `group(..)` output works directly.
macro_rules! tuple_kids {
    ($($name:ident),+) => {
        impl<$($name: IntoKids),+> IntoKids for ($($name,)+) {
            #[allow(non_snake_case)]
            fn push_kids(self, out: &mut Vec<Frag>) {
                let ($($name,)+) = self;
                $($name.push_kids(out);)+
            }
        }
    };
}

tuple_kids!(A);
tuple_kids!(A, B);
tuple_kids!(A, B, C);
tuple_kids!(A, B, C, D);
tuple_kids!(A, B, C, D, E);
tuple_kids!(A, B, C, D, E, F);
tuple_kids!(A, B, C, D, E, F, G);
tuple_kids!(A, B, C, D, E, F, G, H);
tuple_kids!(A, B, C, D, E, F, G, H, I);
tuple_kids!(A, B, C, D, E, F, G, H, I, J);
tuple_kids!(A, B, C, D, E, F, G, H, I, J, K);
tuple_kids!(A, B, C, D, E, F, G, H, I, J, K, L);

/// Wraps a rule's output in a node of the given kind.
pub fn node<'a, O, P>(
    kind: SyntaxKind,
    parser: P,
) -> impl Parser<'a, In<'a>, Frag, Extra<'a>> + Clone
where
    O: IntoKids,
    P: Parser<'a, In<'a>, O, Extra<'a>> + Clone,
{
    parser.map(move |out| {
        let mut kids = Vec::new();
        out.push_kids(&mut kids);
        Frag::Node(kind, kids)
    })
}

/// Matches one token of the given kind.
pub fn tok<'a>(kind: SyntaxKind) -> impl Parser<'a, In<'a>, Frag, Extra<'a>> + Clone {
    any()
        .filter(move |t: &SigToken<'a>| t.kind == kind)
        .map_with(|_, e: &mut MapExtra<'a, '_, In<'a>, Extra<'a>>| Frag::Token(e.span().start))
}

/// Matches one token from a set of kinds.
pub fn tok_in<'a>(
    kinds: &'static [SyntaxKind],
) -> impl Parser<'a, In<'a>, Frag, Extra<'a>> + Clone {
    any()
        .filter(move |t: &SigToken<'a>| kinds.contains(&t.kind))
        .map_with(|_, e: &mut MapExtra<'a, '_, In<'a>, Extra<'a>>| Frag::Token(e.span().start))
}

/// An identifier token.
pub fn ident<'a>() -> impl Parser<'a, In<'a>, Frag, Extra<'a>> + Clone {
    tok(SyntaxKind::IDENT)
}

/// Matches any single token. Used by rules that deliberately keep a region
/// uninterpreted, and by error recovery.
pub fn any_tok<'a>() -> impl Parser<'a, In<'a>, Frag, Extra<'a>> + Clone {
    any().map_with(|_, e: &mut MapExtra<'a, '_, In<'a>, Extra<'a>>| Frag::Token(e.span().start))
}

/// Strips the suffixes Lean allows on a tactic name.
///
/// `simp?` and `simp!` are single identifier tokens, because `?` and `!` are
/// identifier characters in Lean, so matching a name has to ignore them.
pub fn tactic_base_name(text: &str) -> &str {
    text.trim_end_matches(['?', '!'])
}

/// Matches an identifier used as a tactic name, given a set of accepted names.
///
/// Compares against [`tactic_base_name`], so `simp?` matches `"simp"`.
pub fn tactic_name<'a>(
    names: &'static [&'static str],
) -> impl Parser<'a, In<'a>, Frag, Extra<'a>> + Clone {
    any()
        .filter(move |t: &SigToken<'a>| {
            t.kind == SyntaxKind::IDENT && names.contains(&tactic_base_name(t.text))
        })
        .map_with(|_, e: &mut MapExtra<'a, '_, In<'a>, Extra<'a>>| Frag::Token(e.span().start))
}

/// Matches any single token whose kind satisfies `pred`.
pub fn any_tok_if<'a>(
    pred: fn(SyntaxKind) -> bool,
) -> impl Parser<'a, In<'a>, Frag, Extra<'a>> + Clone {
    any()
        .filter(move |t: &SigToken<'a>| pred(t.kind))
        .map_with(|_, e: &mut MapExtra<'a, '_, In<'a>, Extra<'a>>| Frag::Token(e.span().start))
}

/// A separated list that keeps the separator tokens as children, so the tree
/// still describes where the commas were. A trailing separator is allowed.
pub fn sep_list<'a, P>(
    item: P,
    sep: SyntaxKind,
) -> impl Parser<'a, In<'a>, Vec<Frag>, Extra<'a>> + Clone
where
    P: Parser<'a, In<'a>, Frag, Extra<'a>> + Clone + 'a,
{
    item.clone()
        .then(
            tok(sep)
                .then(item)
                .repeated()
                .collect::<Vec<(Frag, Frag)>>(),
        )
        .then(tok(sep).or_not())
        .map(|((first, rest), trailing)| {
            let mut kids = vec![first];
            for (s, i) in rest {
                kids.push(s);
                kids.push(i);
            }
            kids.extend(trailing);
            kids
        })
}

/// Matches a token of the given kind only when it is *immediately* adjacent to
/// the preceding token, with no whitespace between them.
///
/// Lean uses this distinction: `(f x).foo` is a field access, while `f .foo`
/// passes the anonymous constructor `.foo` as an argument.
pub fn adjacent_tok<'a>(kind: SyntaxKind) -> impl Parser<'a, In<'a>, Frag, Extra<'a>> + Clone {
    custom(move |inp: &mut InputRef<'a, '_, In<'a>, Extra<'a>>| {
        let here = inp.cursor();
        let idx = *here.inner();
        let all = inp.full_slice();
        let adjacent = match (idx.checked_sub(1).and_then(|i| all.get(i)), all.get(idx)) {
            (Some(prev), Some(cur)) => {
                cur.kind == kind && prev.offset + prev.text.len() as u32 == cur.offset
            }
            _ => false,
        };
        if adjacent {
            inp.skip();
            Ok(Frag::Token(idx))
        } else {
            Err(Rich::custom(
                inp.span_since(&here),
                format!("expected {kind:?} with no preceding whitespace"),
            ))
        }
    })
}

/// A list whose separator is optional, for constructs Lean lets newlines
/// separate — structure instance fields, most visibly.
pub fn list_maybe_sep<'a, P>(
    item: P,
    sep: SyntaxKind,
) -> impl Parser<'a, In<'a>, Vec<Frag>, Extra<'a>> + Clone
where
    P: Parser<'a, In<'a>, Frag, Extra<'a>> + Clone + 'a,
{
    item.clone()
        .then(
            group((tok(sep).or_not(), item))
                .repeated()
                .collect::<Vec<(Option<Frag>, Frag)>>(),
        )
        .then(tok(sep).or_not())
        .map(|((first, rest), trailing)| {
            let mut kids = vec![first];
            for (s, i) in rest {
                kids.extend(s);
                kids.push(i);
            }
            kids.extend(trailing);
            kids
        })
}

/// Matches a token of the given kind only when whitespace *does* separate it
/// from the preceding token.
///
/// The complement of [`adjacent_tok`]. `(f ..)` passes `..` as an argument
/// meaning "fill in the rest", while `a..b` is a range: spacing is what tells
/// them apart.
pub fn spaced_tok<'a>(kind: SyntaxKind) -> impl Parser<'a, In<'a>, Frag, Extra<'a>> + Clone {
    custom(move |inp: &mut InputRef<'a, '_, In<'a>, Extra<'a>>| {
        let here = inp.cursor();
        let idx = *here.inner();
        let all = inp.full_slice();
        let spaced = match (idx.checked_sub(1).and_then(|i| all.get(i)), all.get(idx)) {
            (Some(prev), Some(cur)) => {
                cur.kind == kind && prev.offset + prev.text.len() as u32 != cur.offset
            }
            (None, Some(cur)) => cur.kind == kind,
            _ => false,
        };
        if spaced {
            inp.skip();
            Ok(Frag::Token(idx))
        } else {
            Err(Rich::custom(
                inp.span_since(&here),
                format!("expected {kind:?} preceded by whitespace"),
            ))
        }
    })
}

/// True if this token opens a bracketed group, returning its closer.
pub fn closer_for(kind: SyntaxKind) -> Option<SyntaxKind> {
    use SyntaxKind::*;
    Some(match kind {
        L_PAREN => R_PAREN,
        L_BRACE => R_BRACE,
        L_BRACKET => R_BRACKET,
        L_ANGLE_ANON => R_ANGLE_ANON,
        L_STRICT_IMPLICIT => R_STRICT_IMPLICIT,
        L_DOUBLE_BRACKET => R_DOUBLE_BRACKET,
        _ => return None,
    })
}

/// True if this token closes a bracketed group.
pub fn is_closer(kind: SyntaxKind) -> bool {
    use SyntaxKind::*;
    matches!(
        kind,
        R_PAREN | R_BRACE | R_BRACKET | R_ANGLE_ANON | R_STRICT_IMPLICIT | R_DOUBLE_BRACKET
    )
}

/// Zero-width check that the next token is indented past the enclosing
/// position — Lean's `colGt`.
///
/// Tokens later on the same line as the enclosing position always satisfy this,
/// so one column comparison covers both "same line" and "properly indented
/// continuation".
pub fn col_gt<'a>() -> impl Parser<'a, In<'a>, (), Extra<'a>> + Clone {
    custom(|inp: &mut InputRef<'a, '_, In<'a>, Extra<'a>>| {
        let min = *inp.ctx();
        let here = inp.cursor();
        match inp.peek() {
            Some(t) if t.col > min => Ok(()),
            _ => Err(Rich::custom(
                inp.span_since(&here),
                format!("expected a token indented past column {min}"),
            )),
        }
    })
}

/// Reads the column of the next token without consuming it.
pub fn peek_col<'a>() -> impl Parser<'a, In<'a>, u32, Extra<'a>> + Clone {
    custom(|inp: &mut InputRef<'a, '_, In<'a>, Extra<'a>>| {
        let here = inp.cursor();
        match inp.peek() {
            Some(t) => Ok(t.col),
            None => Err(Rich::custom(
                inp.span_since(&here),
                "unexpected end of input",
            )),
        }
    })
}

/// A run of tokens, bracket-balanced, stopping before any token that `stop`
/// accepts at bracket depth zero.
///
/// This is how the parser handles regions it deliberately does not interpret —
/// the arguments of a tactic, the right-hand side of a `notation` — without
/// losing them from the tree. The run also stops when indentation falls back to
/// the enclosing block, so it can never swallow the next item.
pub fn balanced_run<'a>(
    kind: SyntaxKind,
    stop: fn(SyntaxKind) -> bool,
    allow_empty: bool,
) -> impl Parser<'a, In<'a>, Frag, Extra<'a>> + Clone {
    run(kind, stop, allow_empty, true)
}

/// A balanced run for a region that is *already* inside brackets, where Lean
/// imposes no column constraint.
///
/// `@[to_additive` followed by its argument on the next line at column 0 is
/// legal, and a dedent-terminated run rejects it: the enclosing bracket was
/// consumed before the run started, so the run sees depth zero and applies a
/// rule that does not apply.
pub fn bracketed_run<'a>(
    kind: SyntaxKind,
    stop: fn(SyntaxKind) -> bool,
    allow_empty: bool,
) -> impl Parser<'a, In<'a>, Frag, Extra<'a>> + Clone {
    run(kind, stop, allow_empty, false)
}

fn run<'a>(
    kind: SyntaxKind,
    stop: fn(SyntaxKind) -> bool,
    allow_empty: bool,
    stop_on_dedent: bool,
) -> impl Parser<'a, In<'a>, Frag, Extra<'a>> + Clone {
    custom(move |inp: &mut InputRef<'a, '_, In<'a>, Extra<'a>>| {
        let min = *inp.ctx();
        let start = inp.cursor();
        let mut kids: Vec<Frag> = Vec::new();
        let mut depth: Vec<SyntaxKind> = Vec::new();
        while let Some(t) = inp.peek() {
            if depth.is_empty() {
                // Dedent ends the run: the token belongs to an outer block.
                if stop_on_dedent && t.col <= min {
                    break;
                }
                if stop(t.kind) || is_closer(t.kind) {
                    break;
                }
            }
            let idx = *inp.cursor().inner();
            inp.skip();
            if let Some(close) = closer_for(t.kind) {
                depth.push(close);
            } else if is_closer(t.kind) {
                // Tolerate mismatches: any closer pops, so a stray `)` cannot
                // make the run consume the rest of the file.
                depth.pop();
            }
            kids.push(Frag::Token(idx));
        }
        if kids.is_empty() && !allow_empty {
            return Err(Rich::custom(
                inp.span_since(&start),
                "expected at least one token",
            ));
        }
        Ok(Frag::Node(kind, kids))
    })
}

/// Parses a sequence of layout-sensitive items, Lean's indentation-delimited
/// block.
///
/// The first item's column becomes the block's threshold: later items must
/// start at that column or beyond, and everything *inside* an item must be
/// indented strictly past it. An item that fails to parse ends the block rather
/// than failing it, provided at least one item succeeded — which is what lets
/// a nested `by` block stop cleanly when the outer block's next tactic dedents.
///
/// `require_indent` selects Lean's `colGt` (true) or `colGe` (false) rule for
/// where the block itself may begin. Neither permits a block starting to the
/// left of the enclosing position.
pub fn layout_block<'a, P>(
    kind: SyntaxKind,
    item: P,
    separators: &'static [SyntaxKind],
    require_indent: bool,
) -> impl Parser<'a, In<'a>, Frag, Extra<'a>> + Clone
where
    P: Parser<'a, In<'a>, Frag, Extra<'a>> + Clone + 'a,
{
    custom(move |inp: &mut InputRef<'a, '_, In<'a>, Extra<'a>>| {
        let enclosing = *inp.ctx();
        let start = inp.cursor();
        let Some(first) = inp.peek() else {
            return Err(Rich::custom(
                inp.span_since(&start),
                "expected an indented block, found end of input",
            ));
        };
        // A `by` or `do` block must be indented strictly past its enclosing
        // position (`colGt`). `match` alternatives, declaration equations and
        // `with` alternatives need only reach it (`colGe`), since Lean accepts a
        // leading `|` level with — or back at column 0 relative to — the syntax
        // introducing it. Neither may start *before* it: that is what stops a
        // tactic from claiming the alternatives of an enclosing block.
        let too_shallow = if require_indent {
            first.col <= enclosing
        } else {
            first.col < enclosing
        };
        if too_shallow {
            return Err(Rich::custom(
                inp.span_since(&start),
                format!(
                    "expected a block indented past column {enclosing}, found one at column {}",
                    first.col
                ),
            ));
        }
        let base = first.col;
        let mut kids: Vec<Frag> = Vec::new();
        loop {
            // An item continues the block if it lines up with the first item,
            // or if it is merely indented past the enclosing position. The
            // second case matters when the first item shares a line with its
            // introducer, as in
            //
            // ```lean
            //   calc a = b := h1
            //     _ = c := h2
            // ```
            //
            // where the later steps sit at a *smaller* column than the first.
            let item_col = match inp.peek() {
                Some(t) if t.col >= base || t.col > enclosing => t.col,
                _ => break,
            };
            let checkpoint = inp.save();
            // Each item's own column is the threshold for its contents, so the
            // next item can never be absorbed as a continuation of this one.
            match inp.parse(item.clone().with_ctx(item_col)) {
                Ok(frag) => kids.push(frag),
                Err(err) => {
                    inp.rewind(checkpoint);
                    if kids.is_empty() {
                        return Err(err);
                    }
                    break;
                }
            }
            // Separators (`;`) are optional; newlines separate just as well.
            while let Some(t) = inp.peek() {
                if separators.contains(&t.kind) && t.col >= base {
                    let idx = *inp.cursor().inner();
                    inp.skip();
                    kids.push(Frag::Token(idx));
                } else {
                    break;
                }
            }
        }
        Ok(Frag::Node(kind, kids))
    })
}

/// Runs `parser` with the indentation threshold set from the column of the next
/// token, establishing a new layout position — Lean's `withPosition`.
pub fn with_position<'a, P>(parser: P) -> impl Parser<'a, In<'a>, Frag, Extra<'a>> + Clone
where
    P: Parser<'a, In<'a>, Frag, Extra<'a>> + Clone + 'a,
{
    peek_col().then_with_ctx(parser).map(|(_, frag)| frag)
}
