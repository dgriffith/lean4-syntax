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

/// Error type, unit state, and a [`Ctx`] carrying what the parser needs to know
/// about where it is.
pub type Extra<'a> = extra::Full<Rich<'a, SigToken<'a>>, (), Ctx>;

/// What the parser needs to know about its position, threaded through chumsky's
/// context parameter.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Ctx {
    /// The indentation threshold: a continuation token must be indented past
    /// this column. Lean's `colGt`.
    pub col: u32,
    /// Whether a trailing `do` block may be an application argument.
    ///
    /// `f do …` is legal Lean, but `for x in xs do …` is not an application of
    /// `xs` to a `do` block — so this is false while parsing a loop's
    /// collection, and true elsewhere.
    pub trailing_do: bool,
    /// Whether a top-level comma ends a tactic.
    ///
    /// True inside a comma-separated list, where `⟨by simp, by ring⟩` has two
    /// proofs and the first `by` block must end at the comma. False elsewhere,
    /// because `use 1, 2` and `exists a, b` pass comma-separated arguments to a
    /// single tactic — which is why ending a tactic at every comma cost 2.6% of
    /// the mathlib clean rate when it was tried unconditionally (#18).
    ///
    /// A comma inside brackets needs no help from this: `run` tracks bracket
    /// depth, so `simp [a, b]` and `rw [h₁, h₂]` are already safe.
    pub comma_stops: bool,
}

impl Default for Ctx {
    fn default() -> Ctx {
        Ctx {
            col: 0,
            trailing_do: true,
            comma_stops: false,
        }
    }
}

impl Ctx {
    /// The same context at a new indentation threshold.
    pub fn at(self, col: u32) -> Ctx {
        Ctx { col, ..self }
    }
}

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

/// A field name after a `.`.
///
/// Keywords are not reserved there, and mathlib leans on it: `.forall` (783
/// uses), `.exists` (772), `.rec` (493), `.from`, `.def`, `.module`, `.then`,
/// `.end`. This only comes up after a closing bracket — the lexer folds `x.rec`
/// into one identifier token, since an identifier absorbs a `.` followed by an
/// identifier start, so it is `(h : T).module` and `xs[i].forall` that need it.
pub fn field_name<'a>() -> impl Parser<'a, In<'a>, Frag, Extra<'a>> + Clone {
    any_tok_if(|k| k == SyntaxKind::IDENT || k.is_keyword())
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

/// Matches an identifier whose text is one of `names`.
///
/// Compares against [`tactic_base_name`], so `simp?` matches `"simp"`. Used for
/// tactic names, and for the handful of notations that are identifiers rather
/// than symbols — `𝔼 y, f y` among them.
pub fn ident_named<'a>(
    names: &'static [&'static str],
) -> impl Parser<'a, In<'a>, Frag, Extra<'a>> + Clone {
    any()
        .filter(move |t: &SigToken<'a>| {
            t.kind == SyntaxKind::IDENT && names.contains(&tactic_base_name(t.text))
        })
        .map_with(|_, e: &mut MapExtra<'a, '_, In<'a>, Extra<'a>>| Frag::Token(e.span().start))
}

/// Matches a token of the given kind whose text also satisfies `pred`.
pub fn tok_if_text<'a>(
    kind: SyntaxKind,
    pred: fn(&str) -> bool,
) -> impl Parser<'a, In<'a>, Frag, Extra<'a>> + Clone {
    any()
        .filter(move |t: &SigToken<'a>| t.kind == kind && pred(t.text))
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
    // Inside a comma-separated list, a top-level comma ends a tactic: the first
    // `by` block of `⟨by simp, by ring⟩` stops at the comma rather than taking
    // `, by ring` as more arguments for `simp`. See `Ctx::comma_stops`.
    let item = if sep == SyntaxKind::COMMA {
        with_comma_stops(item).boxed()
    } else {
        item.boxed()
    };
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
/// **Any `repeated()` over tokens that could begin a new line needs this
/// guard.** Five separate bugs in this parser have come from omitting it: an
/// application absorbing the following line, `intros` claiming the next tactic
/// as a pattern, an import list swallowing the next command's name, a `have`
/// eating its own body, and `at hA` taking the following `rw` as another
/// hypothesis. The symptom is always the same — the construct parses in
/// isolation and fails in place.
///
/// Tokens later on the same line as the enclosing position always satisfy this,
/// so one column comparison covers both "same line" and "properly indented
/// continuation".
pub fn col_gt<'a>() -> impl Parser<'a, In<'a>, (), Extra<'a>> + Clone {
    custom(|inp: &mut InputRef<'a, '_, In<'a>, Extra<'a>>| {
        let min = inp.ctx().col;
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

/// Reads the column of the next token and returns the context anchored there,
/// for establishing a new layout position.
pub fn peek_ctx<'a>() -> impl Parser<'a, In<'a>, Ctx, Extra<'a>> + Clone {
    custom(|inp: &mut InputRef<'a, '_, In<'a>, Extra<'a>>| {
        let here = inp.cursor();
        match inp.peek() {
            Some(t) => Ok(inp.ctx().at(t.col)),
            None => Err(Rich::custom(
                inp.span_since(&here),
                "unexpected end of input",
            )),
        }
    })
}

/// Runs `parser` with a trailing `do` argument disallowed.
///
/// Used for a loop's collection: in `for x in xs do …` the `do` opens the loop
/// body, and reading it as an argument of `xs` makes the loop unparsable.
pub fn without_trailing_do<'a, P, O>(parser: P) -> impl Parser<'a, In<'a>, O, Extra<'a>> + Clone
where
    P: Parser<'a, In<'a>, O, Extra<'a>> + Clone + 'a,
{
    custom(move |inp: &mut InputRef<'a, '_, In<'a>, Extra<'a>>| {
        let ctx = Ctx {
            trailing_do: false,
            ..*inp.ctx()
        };
        inp.parse(parser.clone().with_ctx(ctx))
    })
}

/// Zero-width check that a trailing `do` argument is permitted here.
pub fn trailing_do_allowed<'a>() -> impl Parser<'a, In<'a>, (), Extra<'a>> + Clone {
    custom(|inp: &mut InputRef<'a, '_, In<'a>, Extra<'a>>| {
        if inp.ctx().trailing_do {
            Ok(())
        } else {
            let here = inp.cursor();
            Err(Rich::custom(
                inp.span_since(&here),
                "a trailing `do` cannot be an argument here",
            ))
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
    run(kind, stop, allow_empty, true, false)
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
    run(kind, stop, allow_empty, false, false)
}

/// [`balanced_run`], additionally ending at a top-level comma wherever
/// [`Ctx::comma_stops`] says a comma separates items.
///
/// This is for a tactic's arguments, which is the only region where the question
/// arises: `⟨by simp, by ring⟩` has two proofs, and without this the first
/// `simp` takes `, by ring` as its own arguments and the anonymous constructor
/// ends up with one child instead of two.
pub fn tactic_arg_run<'a>(
    kind: SyntaxKind,
    stop: fn(SyntaxKind) -> bool,
    allow_empty: bool,
) -> impl Parser<'a, In<'a>, Frag, Extra<'a>> + Clone {
    run(kind, stop, allow_empty, true, true)
}

/// Runs `parser` with a top-level comma ending any tactic inside it.
pub fn with_comma_stops<'a, P, O>(parser: P) -> impl Parser<'a, In<'a>, O, Extra<'a>> + Clone
where
    P: Parser<'a, In<'a>, O, Extra<'a>> + Clone + 'a,
{
    custom(move |inp: &mut InputRef<'a, '_, In<'a>, Extra<'a>>| {
        let ctx = Ctx {
            comma_stops: true,
            ..*inp.ctx()
        };
        inp.parse(parser.clone().with_ctx(ctx))
    })
}

fn run<'a>(
    kind: SyntaxKind,
    stop: fn(SyntaxKind) -> bool,
    allow_empty: bool,
    stop_on_dedent: bool,
    stop_at_comma: bool,
) -> impl Parser<'a, In<'a>, Frag, Extra<'a>> + Clone {
    custom(move |inp: &mut InputRef<'a, '_, In<'a>, Extra<'a>>| {
        let min = inp.ctx().col;
        let comma_stops_here = stop_at_comma && inp.ctx().comma_stops;
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
                // A comma ends the run only where a comma separates items;
                // see `Ctx::comma_stops`.
                if comma_stops_here && t.kind == SyntaxKind::COMMA {
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
        let enclosing = inp.ctx().col;
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
            let item_ctx = inp.ctx().at(item_col);
            match inp.parse(item.clone().with_ctx(item_ctx)) {
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

/// Runs `parser` with the indentation threshold relaxed by one column, turning
/// a `colGt` requirement into `colGe`.
///
/// A match alternative's tactic block may begin at the alternative's own column:
///
/// ```lean
/// | succ pk hpk =>
/// obtain ⟨t, ht⟩ := h
/// ```
///
/// The block is anchored at the `|`, so requiring strictly greater indentation
/// rejects this, and Lean accepts it.
pub fn relax_indent<'a, P>(parser: P) -> impl Parser<'a, In<'a>, Frag, Extra<'a>> + Clone
where
    P: Parser<'a, In<'a>, Frag, Extra<'a>> + Clone + 'a,
{
    custom(move |inp: &mut InputRef<'a, '_, In<'a>, Extra<'a>>| {
        let relaxed = inp.ctx().at(inp.ctx().col.saturating_sub(1));
        inp.parse(parser.clone().with_ctx(relaxed))
    })
}

/// Runs `parser` anchored on its own first token rather than on the enclosing
/// position, so a block need only line up with itself — Lean's `withPosition`
/// combined with `colGe`.
///
/// This is what a `do` body needs. Nothing ties its statements to the syntax
/// that introduced the `do`, and mathlib relies on that:
///
/// ```lean
///   match pα? with | none => pure .none | some _ => do
///   let (.app f a) ← whnfR e | throwError "not abv"
///   …
/// ```
///
/// Here the arm's `|` sits mid-line, so the body at column 2 is nowhere near
/// it; [`relax_indent`] cannot reach that far, since it only gives up one
/// column. Anchoring on the first token still bounds the block — a later token
/// at a smaller column ends it — which is what stops a `do` body from eating
/// the next field of an enclosing structure instance, or the next declaration.
///
/// The threshold only ever *drops*. Taking the first token's column outright
/// raises it whenever a block begins mid-line, which rejects the block's own
/// continuation lines:
///
/// ```lean
///   monotone' := monotone_iff_forall_lt.2 (by
///     simp)
/// ```
///
/// Here the value starts at column 15 and continues at column 4. Anchoring on
/// column 15 threw that away and cost 5.4% of the mathlib clean rate.
pub fn unanchored<'a, P>(parser: P) -> impl Parser<'a, In<'a>, Frag, Extra<'a>> + Clone
where
    P: Parser<'a, In<'a>, Frag, Extra<'a>> + Clone + 'a,
{
    custom(move |inp: &mut InputRef<'a, '_, In<'a>, Extra<'a>>| {
        let first = inp.peek().map(|t| t.col).unwrap_or(0);
        let enclosing = inp.ctx().col;
        let ctx = inp.ctx().at(enclosing.min(first.saturating_sub(1)));
        inp.parse(parser.clone().with_ctx(ctx))
    })
}

/// Like [`unanchored`], for a *value* rather than a layout block: the threshold
/// becomes the value's own first column, not one less.
///
/// A `where` field's value may begin to the left of its field name, and then
/// that column is what bounds it. The distinction from [`unanchored`] is which
/// side of the threshold the following tokens sit on. A `do` body is a layout
/// block that applies `colGt` to its own first item, so its threshold has to be
/// one *below* that item. A term applies `colGt` to its continuations, so its
/// threshold has to be the value's column exactly — one less absorbs the next
/// field:
///
/// ```lean
///   algebraMap :=
///   { toFun _ := PUnit.unit
///     map_one' := rfl }
///   commutes' _ _ := rfl
/// ```
///
/// Here the value starts at column 2, the same column as its own field name. At
/// a threshold of 1, `commutes'` reads as one more argument of the structure
/// instance and its `:=` then fails — 98 files.
pub fn value_anchored<'a, P>(parser: P) -> impl Parser<'a, In<'a>, Frag, Extra<'a>> + Clone
where
    P: Parser<'a, In<'a>, Frag, Extra<'a>> + Clone + 'a,
{
    custom(move |inp: &mut InputRef<'a, '_, In<'a>, Extra<'a>>| {
        let first = inp.peek().map(|t| t.col).unwrap_or(0);
        let ctx = inp.ctx().at(inp.ctx().col.min(first));
        inp.parse(parser.clone().with_ctx(ctx))
    })
}

/// Runs `parser` with the indentation threshold set from the column of the next
/// token, establishing a new layout position — Lean's `withPosition`.
pub fn with_position<'a, P>(parser: P) -> impl Parser<'a, In<'a>, Frag, Extra<'a>> + Clone
where
    P: Parser<'a, In<'a>, Frag, Extra<'a>> + Clone + 'a,
{
    peek_ctx().then_with_ctx(parser).map(|(_, frag)| frag)
}
