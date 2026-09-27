//! The tactic grammar.
//!
//! # One node per shape, not per tactic
//!
//! Lean's tactic vocabulary is open-ended and grows with every library, so a
//! node kind per tactic name would be both enormous and permanently incomplete.
//! Instead this module recognises a small set of *shapes* — `simp`-like,
//! `rw`-like, term-taking, pattern-taking, and so on — and lets the name token
//! identify which tactic it actually is. `Tactic::name()` answers "which
//! tactic", the shape answers "how do I reach its parts".
//!
//! A tactic taking no arguments needs no shape of its own — `rfl`, `trivial`
//! and `constructor` parse as [`TACTIC`] with no argument node, and their name
//! token says which they are. Anything unrecognised parses the same way, with a
//! bracket-balanced [`TACTIC_ARGS`] run holding what the shape did not model. That fallback is load-bearing: it is
//! what keeps a file with an unfamiliar or user-defined tactic parsing, and
//! every structured shape also carries an optional trailing `TACTIC_ARGS` for
//! syntax the shape does not model, so leftovers stay attached to the tactic
//! they belong to instead of being mistaken for the next one.
//!
//! # Layout
//!
//! Sequencing, `<;>`, focus dots and `first | …` are modelled because they
//! govern control flow, and because layout depends on them. The indentation
//! machinery in [`layout_block`] is what lets a nested `by` block end at the
//! right place:
//!
//! ```lean
//! theorem t : p := by
//!   have h : q := by
//!     simp
//!   exact h      -- dedent ends the inner block, not the outer one
//! ```

use super::Grammar;
use super::support::*;
use super::term::{binders, type_spec};
use crate::kind::SyntaxKind::{self, *};
use crate::syntax::Frag;
use chumsky::prelude::*;

// ---- Tactic name tables ----------------------------------------------------
//
// Grouped by shape. A name may appear in only one table; the shapes are tried
// in the order they are combined in `tactic_seq`.

/// Take an optional `only`, an optional lemma list, and an optional location.
const SIMP_LIKE: &[&str] = &[
    "simp",
    "simp_all",
    "simp_arith",
    "simp_wf",
    "dsimp",
    "norm_num",
    "norm_cast",
    "push_cast",
    "field_simp",
    "aesop",
    "linarith",
    "nlinarith",
    "polyrith",
    "positivity",
    "gcongr",
    "tauto",
    "ring_nf",
    "abel",
    "abel_nf",
    "group",
    "decide",
    "omega",
    "measurability",
    "continuity",
    "fun_prop",
    "bound",
];

/// Take a rewrite-rule list, whose entries may be reversed with `←`.
const REWRITE_LIKE: &[&str] = &[
    "rw",
    "rewrite",
    "erw",
    "rwa",
    "simp_rw",
    "nth_rw",
    "nth_rewrite",
];

/// Take a single term.
const TERM_LIKE: &[&str] = &[
    "exact",
    "exact_mod_cast",
    "apply",
    "refine",
    "refine'",
    "convert",
    "convert_to",
    "specialize",
    "change",
    "subst",
    "injection",
    "contrapose",
    "by_cases",
    "rel",
];

/// Take a comma-separated list of terms.
const TERM_LIST_LIKE: &[&str] = &["use", "existsi"];

/// Take a sequence of patterns.
const INTRO_LIKE: &[&str] = &[
    "intro", "intros", "rintro", "rintros", "introv", "ext", "ext1", "funext", "peel", "rcongr",
];

/// Take targets and an optional `with` clause.
const CASES_LIKE: &[&str] = &[
    "cases",
    "cases'",
    "rcases",
    "induction",
    "induction'",
    "interval_cases",
    "fin_cases",
];

/// Introduce a new hypothesis or goal, leading with a name or pattern.
///
/// `obtain` belongs here rather than with the `cases`-like tactics: it leads
/// with the pattern it destructures into, where `rcases h with p` leads with
/// the target `h`. Distinguishing them by name avoids an ambiguity that
/// position alone cannot resolve.
const HAVE_LIKE: &[&str] = &["replace", "set", "obtain", "letI", "haveI"];

/// Name a goal and focus it.
const CASE_LIKE: &[&str] = &["case", "case'", "next"];

/// Enter conversion mode.
const CONV_LIKE: &[&str] = &["conv", "conv_lhs", "conv_rhs"];

/// Apply an inner tactic sequence under some control structure.
const COMBINATOR_LIKE: &[&str] = &[
    "all_goals",
    "any_goals",
    "focus",
    "iterate",
    "rotate_left",
    "rotate_right",
    "on_goal",
    "pick_goal",
    "swap",
];

// ---- Stop conditions -------------------------------------------------------

/// Tokens that end a tactic's argument run at bracket depth zero.
///
/// A comma is not here, because whether it ends a tactic depends on where the
/// tactic is. In `refine ⟨by simp, by ring⟩` the first `by` block must end at
/// the comma; in `use 1, 2` the comma separates arguments of one tactic. Adding
/// `COMMA` unconditionally gets the first case right and the second wrong, which
/// cost 2.6% of the mathlib clean rate when it was tried. The distinction is
/// carried by [`Ctx::comma_stops`] and applied by [`tactic_arg_run`] instead.
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
            SEMICOLON
                | SEQ_FOCUS
                | PIPE
                | COMMA
                | FAT_ARROW
                | COLON_EQ
                // These continue an enclosing *term*, so a `by` block inside
                // one must end before them:
                //
                // ```lean
                //   if h : u = v then by
                //     subst u
                //     exact {Walk.nil}
                //   else ∅
                // ```
                //
                // Without this the generic tactic rule reads `else ∅` as one
                // more tactic and the `if` never finds its `else`. A tactic-mode
                // `if h : c then tac else tac` is unaffected: its `then` and
                // `else` are consumed by its own argument run, which does not
                // consult this.
                | KW_ELSE
                | KW_THEN
                | KW_IN
        )
}

/// Guards the generic tactic rule against tokens that cannot start a tactic.
fn tactic_head<'a>() -> impl Parser<'a, In<'a>, Frag, Extra<'a>> + Clone {
    any_tok_if(|k| !cannot_start_tactic(k))
}

// ---- Shared parts ----------------------------------------------------------

/// `at h₁ h₂ ⊢` or `at *` — where a tactic should act.
fn location<'a>() -> impl Parser<'a, In<'a>, Frag, Extra<'a>> + Clone {
    node(
        LOCATION,
        group((
            tok(KW_AT),
            choice((
                tok(STAR).map(|t| vec![t]),
                // The guard matters: without it, `at hA` followed by `rw [a]`
                // on the next line takes `rw` as another hypothesis.
                col_gt()
                    .ignore_then(tok_in(&[IDENT, TURNSTILE, TURNSTILE_ASCII]))
                    .repeated()
                    .at_least(1)
                    .collect::<Vec<_>>(),
            )),
        )),
    )
}

/// `(config := …)`, kept but not interpreted.
fn config<'a>() -> impl Parser<'a, In<'a>, Frag, Extra<'a>> + Clone {
    node(
        TACTIC_CONFIG,
        group((
            tok(L_PAREN),
            balanced_run(RAW_TOKENS, |_| false, true),
            tok(R_PAREN),
        )),
    )
}

/// `rcases` / `rintro` / `obtain` patterns.
///
/// These are a small language of their own: tuples, alternations, `-` to clear
/// a hypothesis, `@` to include implicit arguments.
fn rcases_pat<'a>(g: &Grammar<'a>) -> impl Parser<'a, In<'a>, Frag, Extra<'a>> + Clone + use<'a> {
    let _ = g;
    recursive(|pat| {
        let atom = choice((
            // `⟨a, b, c⟩`
            node(
                RCASES_TUPLE,
                group((
                    tok(L_ANGLE_ANON),
                    sep_list(pat.clone(), COMMA).or_not(),
                    tok(R_ANGLE_ANON),
                )),
            ),
            // `(a | b)` — parenthesised so an alternation can nest.
            node(
                RCASES_TUPLE,
                group((
                    tok(L_PAREN),
                    sep_list(pat.clone(), COMMA).or_not(),
                    tok(R_PAREN),
                )),
            ),
            // `@h` includes implicit arguments in the pattern.
            node(RCASES_PAT, group((tok(AT), tok_in(&[IDENT, UNDERSCORE])))),
            // `-` discards the hypothesis.
            node(RCASES_PAT, tok(MINUS)),
            node(RCASES_PAT, tok_in(&[IDENT, UNDERSCORE])),
        ));

        // `a | b | c`
        atom.clone()
            .then(group((tok(PIPE), atom)).repeated().collect::<Vec<_>>())
            .map(|(first, rest)| {
                if rest.is_empty() {
                    first
                } else {
                    let mut kids = vec![first];
                    rest.push_kids(&mut kids);
                    Frag::Node(RCASES_ALT, kids)
                }
            })
    })
}

/// The `with` clause of a `cases`-like tactic, in either of its two forms.
///
/// `cases h with | inl a => tac` uses alternatives; `rcases h with ⟨a, b⟩` uses
/// a pattern. Alternatives are tried first because they are the more specific
/// shape — they require a leading `|` *and* a `=>`.
fn with_clause<'a>(
    g: &Grammar<'a>,
    seq: Rec<'a>,
) -> impl Parser<'a, In<'a>, Frag, Extra<'a>> + Clone + use<'a> {
    let alt = node(
        MATCH_ALT,
        group((
            tok(PIPE),
            balanced_run(PATTERNS, ends_alt_pattern, true),
            tok(FAT_ARROW),
            relax_indent(seq),
        )),
    );
    // Two shapes share `with`: `induction`/`cases` take alternatives, and
    // `rcases`/`obtain` take an rcases pattern. The optional tactic that runs in
    // every branch belongs to the *alternatives* shape only — Lean puts it in
    // `inductionAlts` — and keeping it there is what stops it from eating the
    // first pattern of `rcases h with ⟨x, hx⟩ | ⟨y, hy⟩`, which
    // `rcases_with_patterns_is_distinguished_from_alternatives` caught.
    choice((
        group((
            tok(KW_WITH),
            // Kept as raw tokens rather than parsed as a tactic: it stops at
            // the first top-level `|` and at a dedent, which is all that is
            // needed to find the alternatives. Parsing it as a tactic sequence
            // would re-enter the very `Recursive` being defined here, which
            // fails silently.
            balanced_run(RAW_TOKENS, |k| k == PIPE, false).or_not(),
            // `value_anchored`, because the tactic that introduced the `with`
            // is often mid-line while its alternatives are back at the tactic
            // block's own column:
            //
            // ```lean
            //   intro l; induction l with
            //   | nil => rfl
            //   | cons x xs ih => …
            // ```
            //
            // Here `induction` sits at column 12 and the alternatives at 2.
            // `colGe` against column 12 rejects them.
            value_anchored(layout_block(MATCH_ALTS, alt, &[], false)),
        ))
        .map(|(kw, pre, alts)| {
            let mut kids = vec![kw];
            kids.extend(pre);
            kids.push(alts);
            Frag::Node(WITH_CLAUSE, kids)
        }),
        group((tok(KW_WITH), node(PATTERNS, sep_list(rcases_pat(g), COMMA))))
            .map(|(kw, pats)| Frag::Node(WITH_CLAUSE, vec![kw, pats])),
    ))
}

// ---- The grammar -----------------------------------------------------------

/// A `by` block's tactic sequence.
pub fn tactic_seq<'a>(g: &Grammar<'a>) -> BoxedP<'a, Frag> {
    let seq = g.tactic_seq.clone();
    let term = g.term.clone();

    // Trailing syntax a shape does not model. Present only when non-empty, so
    // a fully-understood tactic has no stray node, and an unmodelled tail is
    // visible rather than silently reattached to the following tactic.
    let trailing = tactic_arg_run(TACTIC_ARGS, ends_tactic, false).or_not();

    // `[a, ← b, -c, *]`
    let simp_arg = node(
        SIMP_ARG,
        choice((
            group((tok_in(&[LEFT_ARROW, LEFT_ARROW_ASCII]), term.clone()))
                .map(|(a, t)| Frag::Node(RW_RULE, vec![a, t])),
            group((tok(MINUS), term.clone())).map(|(m, t)| Frag::Node(RW_RULE, vec![m, t])),
            tok(STAR),
            term.clone(),
        )),
    );
    let simp_args = node(
        SIMP_ARG_LIST,
        group((
            tok(L_BRACKET),
            sep_list(simp_arg, COMMA).or_not(),
            tok(R_BRACKET),
        )),
    );

    // `simp only [foo, ← bar] at h ⊢`
    let simp_tactic = node(
        TACTIC_SIMP,
        group((
            ident_named(SIMP_LIKE),
            config().or_not(),
            tok(KW_ONLY).or_not(),
            simp_args.clone().or_not(),
            location().or_not(),
            trailing.clone(),
        )),
    );

    // `rw [foo, ← bar] at h`
    let rw_rule = node(
        RW_RULE,
        group((
            tok_in(&[LEFT_ARROW, LEFT_ARROW_ASCII]).or_not(),
            term.clone(),
        )),
    );
    let rw_tactic = node(
        TACTIC_REWRITE,
        group((
            ident_named(REWRITE_LIKE),
            config().or_not(),
            // `nth_rw 2 [foo]` selects which occurrence to rewrite.
            tok(NUMBER).or_not(),
            node(
                RW_RULE_LIST,
                group((
                    tok(L_BRACKET),
                    sep_list(rw_rule, COMMA).or_not(),
                    tok(R_BRACKET),
                )),
            ),
            location().or_not(),
            trailing.clone(),
        )),
    );

    // `exact h.symm`, `refine ⟨?_, ?_⟩`, `change T with T'`
    let term_tactic = node(
        TACTIC_TERM,
        group((
            ident_named(TERM_LIKE),
            config().or_not(),
            term.clone(),
            group((tok(KW_WITH), term.clone())).or_not(),
            location().or_not(),
            trailing.clone(),
        )),
    );

    // `use 3, 4`; `exists x` — `exists` is a reserved word, so it needs the
    // keyword token rather than a name match.
    let term_list_tactic = node(
        TACTIC_TERM_LIST,
        group((
            choice((ident_named(TERM_LIST_LIKE), tok(KW_EXISTS_KW))),
            sep_list(term.clone(), COMMA),
            trailing.clone(),
        )),
    );

    // `intro x y ⟨a, b⟩`
    // The `col_gt` guard matters as much here as it does for application
    // arguments. Without it,
    //
    // ```lean
    //   simp only [foo]; intros
    //   constructor <;> (symm; assumption)
    // ```
    //
    // reads `constructor` as a pattern of `intros`, because `intros` sits
    // mid-line and the next line is dedented relative to it.
    let intro_tactic = node(
        TACTIC_INTRO,
        group((
            ident_named(INTRO_LIKE),
            col_gt()
                .ignore_then(rcases_pat(g))
                .repeated()
                .collect::<Vec<_>>(),
            trailing.clone(),
        )),
    );

    // `cases h with | inl a => tac`; `rcases h with ⟨x, hx⟩`;
    let cases_target = group((
        group((tok_in(&[IDENT, UNDERSCORE]), tok(COLON))).or_not(),
        term.clone(),
    ));

    // `induction xs using List.rec with …`; `obtain ⟨a, b⟩ : T := e`
    let cases_tactic = node(
        TACTIC_CASES,
        group((
            ident_named(CASES_LIKE),
            config().or_not(),
            // A target may name the equation hypothesis: `induction hg : s ∪ t`
            // and `cases h : e` both bind the case's defining equation. The
            // label stays a sibling of its term rather than wrapping it, so the
            // terms remain direct children of `TACTIC_TARGETS` — which is what
            // `terms_in` reads, and wrapping them would silently empty.
            node(
                TACTIC_TARGETS,
                group((
                    cases_target.clone(),
                    group((tok(COMMA), cases_target))
                        .repeated()
                        .collect::<Vec<_>>(),
                )),
            )
            .or_not(),
            group((tok(KW_USING), term.clone()))
                .map(|(kw, t)| Frag::Node(USING_CLAUSE, vec![kw, t]))
                .or_not(),
            // `induction n generalizing m` revert extra hypotheses first.
            group((
                tok(KW_GENERALIZING),
                col_gt()
                    .ignore_then(tok(IDENT))
                    .repeated()
                    .at_least(1)
                    .collect::<Vec<_>>(),
            ))
            .map(|(kw, ids)| {
                let mut kids = vec![kw];
                kids.extend(ids);
                Frag::Node(USING_CLAUSE, kids)
            })
            .or_not(),
            with_clause(g, seq.clone()).or_not(),
            trailing.clone(),
        )),
    );

    // `have h : T := e`, `have h : T`, `suffices h : T by tac`, `set x := e with hx`
    let have_tactic = node(
        TACTIC_HAVE,
        group((
            choice((
                tok_in(&[KW_HAVE, KW_SUFFICES, KW_LET]),
                ident_named(HAVE_LIKE),
            )),
            rcases_pat(g).or_not(),
            col_gt().ignore_then(binders(g)).or_not(),
            // `suffices h : T from e` names the statement; `suffices T from e`
            // does not, so a bare term has to be accepted as the statement.
            // Wrapped in `TYPE_SPEC` so it is reachable the same way either
            // form is.
            choice((type_spec(g), node(TYPE_SPEC, term.clone()))).or_not(),
            group((tok(COLON_EQ), term.clone())).or_not(),
            group((tok(KW_FROM), term.clone())).or_not(),
            group((tok(KW_WITH), tok_in(&[IDENT, UNDERSCORE]))).or_not(),
            trailing.clone(),
        )),
    );

    // `case inl h => tac`, `next x => tac`
    let case_tactic = node(
        TACTIC_CASE,
        group((
            ident_named(CASE_LIKE),
            node(
                CASE_ARGS,
                col_gt()
                    .ignore_then(tok_in(&[IDENT, UNDERSCORE, NUMBER]))
                    .repeated()
                    .collect::<Vec<_>>(),
            ),
            tok(FAT_ARROW),
            seq.clone(),
        )),
    );

    // `conv at h in pat => rw [foo]`
    let conv_tactic = node(
        TACTIC_CONV,
        group((
            ident_named(CONV_LIKE),
            location().or_not(),
            group((tok(KW_IN), term.clone())).or_not(),
            tok(FAT_ARROW),
            seq.clone(),
        )),
    );

    // `show T`
    let show_tactic = node(
        TACTIC_SHOW,
        group((tok(KW_SHOW), term.clone(), trailing.clone())),
    );

    // `calc` in tactic position is the term-level `calc`; rewind so the term
    // parser sees its own leading keyword.
    let calc_tactic = node(TACTIC_CALC, tok(KW_CALC).rewind().ignore_then(term.clone()));

    // `all_goals simp`, `iterate 3 rw [foo]`, `try ring`, `repeat assumption`
    let combinator_tactic = node(
        TACTIC_COMBINATOR_APP,
        group((
            choice((ident_named(COMBINATOR_LIKE), tok_in(&[KW_TRY, KW_REPEAT]))),
            tok(NUMBER).or_not(),
            seq.clone(),
        )),
    );

    // The fallback. `induction`-style `with | alt` blocks are handled here too,
    // so an unrecognised tactic taking alternatives still parses structurally.
    let generic_alt = node(
        MATCH_ALT,
        group((
            tok(PIPE),
            balanced_run(PATTERNS, ends_alt_pattern, true),
            tok(FAT_ARROW),
            relax_indent(seq.clone()),
        )),
    );
    let generic = node(
        TACTIC,
        group((
            tactic_head(),
            tactic_arg_run(TACTIC_ARGS, ends_tactic, false).or_not(),
            layout_block(MATCH_ALTS, generic_alt, &[], false).or_not(),
        )),
    );

    // Structured shapes first, generic last. Within the structured group,
    // order matters only where one shape's prefix could match another's; the
    // name tables are disjoint, so mostly it does not.
    let structured = choice((
        simp_tactic,
        rw_tactic,
        term_tactic,
        term_list_tactic,
        intro_tactic,
        cases_tactic,
        have_tactic,
        case_tactic,
        conv_tactic,
        show_tactic,
        calc_tactic,
        combinator_tactic,
    ))
    .boxed();

    let base = choice((
        // `· tac` — focus on the first goal. Lean uses `·` for this; `•` is
        // scalar multiplication, so it must not be treated as a focus dot.
        node(TACTIC_FOCUS, group((tok(CDOT), seq.clone()))),
        // `(tac; tac)` — an explicit block.
        node(
            TACTIC_SEQ_BRACKETED,
            group((tok(L_PAREN), seq.clone(), tok(R_PAREN))),
        ),
        // `{ tac; tac }` — the same thing in braces, which is how mathlib
        // focuses a goal after `refine ⟨?_, ?_⟩` and what `<;> { … }` applies
        // to every goal. Braces impose no column constraint on the tactics
        // inside, so the sequence is `relax_indent`ed: the closing `}` is the
        // delimiter, not the indentation.
        node(
            TACTIC_SEQ_BRACKETED,
            group((tok(L_BRACE), relax_indent(seq.clone()), tok(R_BRACE))),
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
        structured,
        generic,
    ))
    .boxed();

    // `tac <;> [t₁; t₂]` applies one tactic per goal the left produced, rather
    // than the same tactic to all of them.
    let per_goal = node(
        TACTIC_SEQ_BRACKETED,
        group((tok(L_BRACKET), seq.clone(), tok(R_BRACKET))),
    );

    // `tac <;> tac` applies the right tactic to every goal the left produced.
    let item = base
        .clone()
        .then(
            group((tok(SEQ_FOCUS), choice((per_goal, base.clone()))))
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
