//! The term grammar.
//!
//! Shape of the layering, innermost first:
//!
//! 1. `atom` — a self-contained term. Lean's "big" terms (`fun`, `let`, `do`,
//!    `match`, …) are atoms whose bodies run greedily rightwards, which is what
//!    makes `f fun x => e` and `∀ x, p x → q` both come out right.
//! 2. `trailers` — postfix `.1`, `.field`, `|>.f`, `.{u}`.
//! 3. `app` — juxtaposition, the tightest binding form. Arguments must satisfy
//!    `colGt`, so a dedented line can never be absorbed as an argument.
//! 4. `pratt` — the operator precedence table, over `app` as its atom.

use super::Grammar;
use super::support::*;
use crate::kind::SyntaxKind::{self, *};

use crate::syntax::Frag;
use chumsky::input::MapExtra;
use chumsky::pratt::{infix, left, postfix, prefix, right};
use chumsky::prelude::*;

/// Builds an infix node. A single function item, so every operator entry in the
/// table shares one type and they can live in the same `Vec`.
fn mk_infix<'a>(
    lhs: Frag,
    op: Frag,
    rhs: Frag,
    _: &mut MapExtra<'a, '_, In<'a>, Extra<'a>>,
) -> Frag {
    Frag::Node(INFIX_TERM, vec![lhs, op, rhs])
}

/// Builds a function-arrow node, kept distinct from other infix operators
/// because it is the one every type signature is made of.
fn mk_arrow<'a>(
    lhs: Frag,
    op: Frag,
    rhs: Frag,
    _: &mut MapExtra<'a, '_, In<'a>, Extra<'a>>,
) -> Frag {
    Frag::Node(ARROW_TERM, vec![lhs, op, rhs])
}

fn mk_prefix<'a>(op: Frag, rhs: Frag, _: &mut MapExtra<'a, '_, In<'a>, Extra<'a>>) -> Frag {
    Frag::Node(PREFIX_TERM, vec![op, rhs])
}

fn mk_postfix<'a>(lhs: Frag, op: Frag, _: &mut MapExtra<'a, '_, In<'a>, Extra<'a>>) -> Frag {
    Frag::Node(POSTFIX_TERM, vec![lhs, op])
}

/// An infix operator that may carry a bracketed parameter.
///
/// mathlib's bundled-morphism arrows are written this way — `M →ₗ[R] N`,
/// `M ⊗[R] N` — so the operator token is followed by `[…]` before its right
/// operand. Taking `kinds` by `&'static [_]` keeps every call the same type, so
/// the entries can share one table.
fn param_op<'a>(
    kinds: &'static [SyntaxKind],
    params: BoxedP<'a, Frag>,
) -> impl Parser<'a, In<'a>, Frag, Extra<'a>> + Clone + use<'a> {
    node(OPERATOR, group((tok_in(kinds), params.or_not())))
}

/// `: T`
pub fn type_spec<'a>(
    g: &Grammar<'a>,
) -> impl Parser<'a, In<'a>, Frag, Extra<'a>> + Clone + use<'a> {
    node(TYPE_SPEC, group((tok(COLON), g.term.clone())))
}

/// A bracketed binder: `(x : T)`, `{x : T}`, `⦃x : T⦄`, `[Inst]`.
///
/// Separate from [`binder`] because a dependent arrow may only be introduced by
/// a bracketed binder — `x → y` is an ordinary arrow between two references.
pub fn bracket_binder<'a>(
    g: &Grammar<'a>,
) -> impl Parser<'a, In<'a>, Frag, Extra<'a>> + Clone + use<'a> {
    let term = g.term.clone();
    let names = tok_in(&[IDENT, UNDERSCORE])
        .repeated()
        .at_least(1)
        .collect::<Vec<_>>();

    let default_value = node(
        DEFAULT_VALUE,
        group((tok_in(&[COLON_EQ, DOT_DOT]), term.clone().or_not())),
    );

    choice((
        node(
            PAREN_BINDER,
            group((
                tok(L_PAREN),
                names.clone(),
                type_spec(g).or_not(),
                default_value.or_not(),
                tok(R_PAREN),
            )),
        ),
        node(
            IMPLICIT_BINDER,
            group((
                tok(L_BRACE),
                names.clone(),
                type_spec(g).or_not(),
                tok(R_BRACE),
            )),
        ),
        node(
            STRICT_IMPLICIT_BINDER,
            group((
                tok(L_STRICT_IMPLICIT),
                names.clone(),
                type_spec(g).or_not(),
                tok(R_STRICT_IMPLICIT),
            )),
        ),
        // `[Monad m]` and the named form `[inst : Monad m]`.
        node(
            INST_BINDER,
            group((
                tok(L_BRACKET),
                group((tok(IDENT), tok(COLON))).or_not(),
                term.clone(),
                tok(R_BRACKET),
            )),
        ),
    ))
}

/// Any binder, including a bare name and destructuring patterns.
pub fn binder<'a>(g: &Grammar<'a>) -> impl Parser<'a, In<'a>, Frag, Extra<'a>> + Clone + use<'a> {
    let term = g.term.clone();
    choice((
        bracket_binder(g),
        // `fun ⟨a, b⟩ => …`
        node(
            ANON_CTOR,
            group((
                tok(L_ANGLE_ANON),
                sep_list(term.clone(), COMMA).or_not(),
                tok(R_ANGLE_ANON),
            )),
        ),
        // `fun (a, b) => a + b` destructures a pair. A parenthesised *binder*
        // is tried first, so `(x : T)` is unaffected — it fails here only at the
        // comma.
        node(
            TUPLE,
            group((tok(L_PAREN), sep_list(term.clone(), COMMA), tok(R_PAREN))),
        ),
        node(SIMPLE_BINDER, tok_in(&[IDENT, UNDERSCORE])),
    ))
}

/// One or more binders.
pub fn binders<'a>(g: &Grammar<'a>) -> impl Parser<'a, In<'a>, Frag, Extra<'a>> + Clone + use<'a> {
    node(
        BINDERS,
        binder(g).repeated().at_least(1).collect::<Vec<_>>(),
    )
}

/// Zero or more binders.
pub fn binders_opt<'a>(
    g: &Grammar<'a>,
) -> impl Parser<'a, In<'a>, Frag, Extra<'a>> + Clone + use<'a> {
    node(BINDERS, binder(g).repeated().collect::<Vec<_>>())
}

/// `| pat, pat => body`, the alternative shared by `match` and `fun`.
pub fn match_alts<'a>(
    g: &Grammar<'a>,
) -> impl Parser<'a, In<'a>, Frag, Extra<'a>> + Clone + use<'a> {
    let term = g.term.clone();
    let alt = node(
        MATCH_ALT,
        group((
            tok(DOC_COMMENT).or_not(),
            tok(PIPE),
            node(PATTERNS, sep_list(term.clone(), COMMA)),
            tok(FAT_ARROW),
            term.clone(),
        )),
    );
    // `colGe`, not `colGt`: Lean accepts alternatives back at column 0 even
    // when the `match` itself sits mid-line.
    layout_block(MATCH_ALTS, alt, &[], false)
}

/// The term parser. Defines everything from literals up to the operator table.
pub fn term<'a>(g: &Grammar<'a>) -> BoxedP<'a, Frag> {
    let term = g.term.clone();

    // ---- Simple atoms ------------------------------------------------------

    let reference = node(REF, ident());
    let literal = node(
        LITERAL,
        tok_in(&[NUMBER, SCIENTIFIC, STRING, RAW_STRING, CHAR, NAME_LIT]),
    );
    let hole = node(HOLE, tok(UNDERSCORE));
    // `(f ..)` leaves the remaining arguments to be inferred. Requiring
    // whitespace keeps `a..b` a range rather than two arguments.
    let ellipsis = node(HOLE, spaced_tok(DOT_DOT));
    // `?x` and `?_` — the latter is how `refine` marks the holes it leaves.
    let synthetic_hole = node(
        SYNTHETIC_HOLE,
        group((tok(QUESTION), tok_in(&[IDENT, UNDERSCORE]))),
    );
    let sorry = node(SORRY_TERM, tok(KW_SORRY));
    // Only `·` is the placeholder dot. `•` is scalar multiplication, and is an
    // infix operator rather than an atom.
    let cdot = node(CDOT_TERM, tok(CDOT));
    // `.mk`, `.none` — constructor names resolved from the expected type.
    let dot_ident = node(DOT_IDENT, group((tok(DOT), ident())));

    // `Type`, `Type u`, `Type*`, `Sort 0`, `Prop`.
    let sort = node(
        SORT,
        group((
            tok_in(&[KW_TYPE, KW_SORT, KW_PROP]),
            tok_in(&[STAR, NUMBER, IDENT, UNDERSCORE]).or_not(),
        )),
    );

    // ---- Bracketed atoms ---------------------------------------------------

    let comma_terms = sep_list(term.clone(), COMMA);

    let paren = choice((
        node(PAREN_TERM, group((tok(L_PAREN), tok(R_PAREN)))),
        // `f (p := e)` passes an argument by name. Distinguishable from an
        // ascription because `:=` and `:` are different tokens.
        node(
            NAMED_ARG,
            group((
                tok(L_PAREN),
                tok(IDENT),
                tok(COLON_EQ),
                term.clone(),
                tok(R_PAREN),
            )),
        ),
        // `(e : T)`, and `(e :)` which ascribes with the expected type.
        node(
            TYPE_ASCRIPTION,
            group((
                tok(L_PAREN),
                term.clone(),
                tok(COLON),
                term.clone().or_not(),
                tok(R_PAREN),
            )),
        ),
        // A tuple needs at least two components, else `(e)` would match here.
        node(
            TUPLE,
            group((
                tok(L_PAREN),
                term.clone(),
                group((tok(COMMA), term.clone()))
                    .repeated()
                    .at_least(1)
                    .collect::<Vec<_>>(),
                tok(COMMA).or_not(),
                tok(R_PAREN),
            )),
        ),
        // An operator section: `(↑)`, `(· + ·)`'s cousin for a bare operator.
        node(
            PAREN_TERM,
            group((
                tok(L_PAREN),
                node(
                    SYMBOL_TERM,
                    any_tok_if(|k| k.is_symbol() && !k.is_delimiter()),
                ),
                tok(R_PAREN),
            )),
        ),
        node(
            PAREN_TERM,
            group((tok(L_PAREN), term.clone(), tok(R_PAREN))),
        ),
    ));

    // A notation character with no specific rule: usable as an atom, so `∞`,
    // `⊤`, `𝟙 X` and the rest of the 292-character tail parse without being
    // enumerated one by one.
    // `f ↑m ↑n` — a coercion in argument position. The operator table handles
    // `↑` at the head of a term, but application arguments come from the atom
    // set, so a coercion needs to be an atom of its own too.
    let coerced = recursive(|coerced| {
        node(
            PREFIX_TERM,
            group((
                tok_in(&[UP_ARROW, COE_FUN, COE_SORT]),
                choice((
                    coerced,
                    node(REF, ident()),
                    node(
                        PAREN_TERM,
                        group((tok(L_PAREN), term.clone(), tok(R_PAREN))),
                    ),
                )),
            )),
        )
    });

    // Curated constants, usable wherever a term is — including as an
    // application argument.
    let constant_term = node(
        SYMBOL_TERM,
        tok_in(&[TOP, BOT, EMPTY_SET, INFINITY, ONE_MORPH, ZERO_MORPH]),
    );

    // A notation character with no rule of its own. Deliberately *not* an
    // argument atom: application is greedy and runs before the operator table,
    // so putting this in the argument set would make `a ⊸ b` parse as
    // `APP(a, ⊸, b)` and the operator would never get a chance. It stays a
    // leading atom, so `𝟙 X` and a bare `∞` still work.
    let symbol_term = node(SYMBOL_TERM, tok(SYMBOL));

    // `$x` and `$(e)` splice a term into a quotation or a `congr(…)` macro.
    let antiquotation = node(
        ANTIQUOTATION,
        group((
            tok(DOLLAR),
            choice((
                tok_in(&[IDENT, UNDERSCORE]),
                node(
                    PAREN_TERM,
                    group((tok(L_PAREN), term.clone(), tok(R_PAREN))),
                ),
            )),
        )),
    );

    // Curated delimiter pairs. These cannot go through the generic fallback:
    // `‖` is the same character at both ends, so it has to be a rule.
    let notation_bracket = choice((
        node(
            NOTATION_BRACKET,
            group((tok(NORM_BAR), term.clone(), tok(NORM_BAR))),
        ),
        node(
            NOTATION_BRACKET,
            group((tok(L_FLOOR), term.clone(), tok(R_FLOOR))),
        ),
        node(
            NOTATION_BRACKET,
            group((tok(L_CEIL), term.clone(), tok(R_CEIL))),
        ),
        node(
            NOTATION_BRACKET,
            group((
                tok(L_DOUBLE_BRACKET),
                sep_list(term.clone(), COMMA).or_not(),
                tok(R_DOUBLE_BRACKET),
            )),
        ),
        node(
            NOTATION_BRACKET,
            group((
                tok(L_LIE),
                sep_list(term.clone(), COMMA).or_not(),
                tok(R_LIE),
            )),
        ),
        node(
            NOTATION_BRACKET,
            group((
                tok(L_ANGLE_INNER),
                sep_list(term.clone(), COMMA).or_not(),
                tok(R_ANGLE_INNER),
            )),
        ),
    ));

    // `#s` — cardinality. Ordered after `array_lit` in the atom list so that
    // `#[1, 2]` stays an array literal rather than `#` applied to a list.
    let card_term = node(PREFIX_TERM, group((tok(HASH), term.clone())));

    // `|x|` — absolute value. This is the one delimiter that collides with
    // structural syntax: `|` also separates match alternatives, `rcases`
    // patterns and `first | …` branches.
    //
    // It is nonetheless safe here, for two reasons. Alternative separators are
    // matched by an explicit `tok(PIPE)` in their own rules, never through the
    // term parser. And a wrong attempt fails cheaply: the required closing `|`
    // means that in
    //
    // ```lean
    // | a => f
    // | b => g
    // ```
    //
    // reading `| b` as an absolute value dies at the `=>` where the closing `|`
    // should be, and the application stops as it should.
    //
    // The one shape that would genuinely be ambiguous is pattern alternation,
    // `| a | b => e`, which this parser does not support yet. Supporting it will
    // need this rule revisited.
    let abs_value = node(
        NOTATION_BRACKET,
        group((tok(PIPE), term.clone(), tok(PIPE))),
    );

    let anon_ctor = node(
        ANON_CTOR,
        group((
            tok(L_ANGLE_ANON),
            comma_terms.clone().or_not(),
            tok(R_ANGLE_ANON),
        )),
    );

    // `![a, b, c]` — matrix and vector notation. Unambiguous, since a leading
    // `!` is not otherwise a term.
    // `![a, b]` vectors and `!![a, b; c, d]` matrices, whose rows are separated
    // by `;`. Unambiguous, since a leading `!` is not otherwise a term.
    let vec_lit = node(
        ARRAY_LIT,
        group((
            // `!` and `!!`, and `!₂` which the lexer decorates into one symbol.
            // Matching on the text rather than on `SYMBOL` generally matters:
            // `M →ₗ[R] N` has the same shape, and treating that as a literal
            // would destroy the parameterised-operator reading.
            choice((
                tok(BANG).repeated().at_least(1).collect::<Vec<_>>(),
                tok_if_text(SYMBOL, |t| t.starts_with('!')).map(|t| vec![t]),
            )),
            tok(L_BRACKET),
            term.clone()
                .then(
                    group((tok_in(&[COMMA, SEMICOLON]), term.clone()))
                        .repeated()
                        .collect::<Vec<_>>(),
                )
                .or_not(),
            tok(R_BRACKET),
        )),
    );

    // `#[a, b]` — core Lean's array literal.
    let array_lit = node(
        ARRAY_LIT,
        group((
            tok(HASH),
            tok(L_BRACKET),
            comma_terms.clone().or_not(),
            tok(R_BRACKET),
        )),
    );

    let list_lit = choice((
        // `[0:10]` and `[0:10:2]` — the ranges `for` loops iterate over.
        node(
            RANGE_LIT,
            group((
                tok(L_BRACKET),
                term.clone().or_not(),
                tok(COLON),
                term.clone().or_not(),
                group((tok(COLON), term.clone())).or_not(),
                tok(R_BRACKET),
            )),
        ),
        node(
            LIST_LIT,
            group((tok(L_BRACKET), comma_terms.clone().or_not(), tok(R_BRACKET))),
        ),
    ));

    // `‹T›` — "the proof of T already in scope".
    let anon_have = node(
        PAREN_TERM,
        group((tok(L_ANON_HAVE), term.clone(), tok(R_ANON_HAVE))),
    );

    // Brace terms are ordered so the discriminating token (`//`, `|`, `:=`,
    // `with`) is reached before a more permissive alternative matches.
    let struct_field = choice((
        node(
            STRUCT_INST_FIELD,
            group((tok(IDENT), tok(COLON_EQ), term.clone())),
        ),
        // Field abbreviation: `{ x, y }` means `{ x := x, y := y }`.
        node(STRUCT_INST_FIELD, tok(IDENT)),
        node(STRUCT_INST_FIELD, tok(DOT_DOT)),
    ));

    let brace = choice((
        node(SET_LIT, group((tok(L_BRACE), tok(R_BRACE)))),
        // `{ x : T // p }`
        node(
            SUBTYPE,
            group((
                tok(L_BRACE),
                tok_in(&[IDENT, UNDERSCORE]),
                type_spec(g).or_not(),
                tok(SLASH_SLASH),
                term.clone(),
                tok(R_BRACE),
            )),
        ),
        // `{ s with x := 1 }`
        node(
            STRUCT_INST,
            group((
                tok(L_BRACE),
                // Several sources are allowed: `{ a, b with f := e }`.
                node(
                    STRUCT_INST_SRC,
                    group((sep_list(term.clone(), COMMA), tok(KW_WITH))),
                ),
                layout_block(STRUCT_FIELD_LIST, struct_field.clone(), &[COMMA], false).or_not(),
                tok(R_BRACE),
            )),
        ),
        // `{ x := 1, y := 2 }`, and the same with fields on separate lines,
        // which Lean accepts without commas.
        node(
            STRUCT_INST,
            group((
                tok(L_BRACE),
                layout_block(
                    STRUCT_FIELD_LIST,
                    node(
                        STRUCT_INST_FIELD,
                        group((
                            tok(IDENT),
                            // `toFun _ := PUnit.unit` — a field may take its own
                            // arguments.
                            binders_opt(g),
                            tok(COLON_EQ),
                            term.clone(),
                        )),
                    ),
                    &[COMMA],
                    false,
                ),
                tok(R_BRACE),
            )),
        ),
        // `{ x | p x }` and `{ x : T | p x }`
        node(
            SET_OF,
            group((
                tok(L_BRACE),
                term.clone(),
                type_spec(g).or_not(),
                tok(PIPE),
                term.clone(),
                tok(R_BRACE),
            )),
        ),
        node(
            SET_LIT,
            group((tok(L_BRACE), comma_terms.clone(), tok(R_BRACE))),
        ),
        // Structure instances mixing assignments with field abbreviations:
        // `{ cmd := c, args, env }` means `args := args, env := env`. Placed
        // after `SET_LIT` so `{a, b}` stays a set literal — the two forms are
        // genuinely ambiguous in surface syntax, and Lean separates them by
        // expected type, which a parser does not have.
        node(
            STRUCT_INST,
            group((
                tok(L_BRACE),
                layout_block(STRUCT_FIELD_LIST, struct_field.clone(), &[COMMA], false),
                tok(R_BRACE),
            )),
        ),
    ));

    // ---- Binding and control atoms ----------------------------------------

    let fun_head = tok_in(&[KW_FUN, LAMBDA]);
    let fun_arrow = tok_in(&[FAT_ARROW, MAPSTO]);

    let fun_term = choice((
        // `fun | 0 => a | n+1 => b`
        node(FUN_ALTS, group((fun_head.clone(), match_alts(g)))),
        node(
            FUN,
            group((
                fun_head.clone(),
                binders(g),
                type_spec(g).or_not(),
                fun_arrow,
                term.clone(),
            )),
        ),
    ));

    // `@f`, and also `@fun (a : T) => e`, which makes a lambda's implicit
    // arguments explicit.
    let at_term = node(
        AT_TERM,
        group((
            tok(AT),
            choice((tok_in(&[IDENT, UNDERSCORE]), fun_term.clone())),
        )),
    );

    // `∃ x > 0, p x` — the relation is sugar for a conjunction. `SYMBOL` is
    // included because a measure-theoretic binder introduces its restriction
    // with notation of its own: `∀ᵐ x ∂μ, p x`.
    let binder_pred = group((
        tok_in(&[
            LT, GT, LE, GE, LE_ASCII, GE_ASCII, NE, MEM, NOT_MEM, SUBSET_EQ, EQ, KW_IN, KW_WITH,
            SYMBOL,
        ]),
        term.clone(),
    ));

    let quantifier = node(
        QUANTIFIER,
        group((
            // Big operators bind variables exactly as the quantifiers do:
            // `∑ i ∈ s, f i` has the shape of `∀ i ∈ s, p i`.
            tok_in(&[
                FORALL,
                KW_FORALL_KW,
                EXISTS,
                KW_EXISTS_KW,
                SIGMA,
                PI,
                BIG_SUM,
                BIG_PROD,
                BIG_UNION,
                BIG_INTER,
                BIG_SUP,
                BIG_INF,
                BIG_OPLUS,
                BIG_OTIMES,
                INTEGRAL,
                // A decorated big operator — `∫ˢ`, `∑'` — lexes as a generic
                // symbol, and still binds variables.
                SYMBOL,
            ])
            // `𝔼 y, f y` — expectation. Its head is a double-struck letter,
            // which Lean lexes as an identifier rather than a symbol.
            .or(ident_named(&["𝔼"])),
            binders(g),
            type_spec(g).or_not(),
            binder_pred.repeated().collect::<Vec<_>>(),
            tok(COMMA),
            term.clone(),
        )),
    );

    // `(x : α) → β x`, which a plain `(e : T)` ascription would otherwise eat.
    let dep_arrow = node(
        DEP_ARROW,
        group((
            bracket_binder(g).repeated().at_least(1).collect::<Vec<_>>(),
            tok_in(&[ARROW, THIN_ARROW]),
            term.clone(),
        )),
    );

    // The left-hand side of `let`: either a name with binders, or a pattern.
    let let_lhs = choice((
        group((tok_in(&[IDENT, UNDERSCORE]), binders_opt(g)))
            .map(|(n, b)| Frag::Node(DECL_ID, vec![n, b])),
        // `have {p} (pp : p.Prime) : p = 2 := …` introduces binders without
        // naming the hypothesis.
        binders(g),
        node(
            ANON_CTOR,
            group((
                tok(L_ANGLE_ANON),
                comma_terms.clone().or_not(),
                tok(R_ANGLE_ANON),
            )),
        ),
        node(
            TUPLE,
            group((tok(L_PAREN), comma_terms.clone(), tok(R_PAREN))),
        ),
    ));

    // `let rec go : Nat → Nat | 0 => 0 | k+1 => go k` defines by equations
    // rather than with `:=`, so both forms are accepted here.
    let let_value = choice((
        node(DECL_BODY, group((tok(COLON_EQ), term.clone()))),
        node(DECL_EQNS, match_alts(g)),
    ));

    // Lean anchors these at the keyword: the value's continuation must be
    // indented past it, and the body need only reach it. Without that anchor
    // the threshold is the enclosing command's column, and
    //
    // ```lean
    //   have ⟨t, ht⟩ := normalize l t
    //   ⟨t, by simp⟩
    // ```
    //
    // reads the body as one more argument of `normalize`.
    let let_term = with_position(node(
        LET_TERM,
        group((
            tok(KW_LET),
            tok(KW_REC).or_not(),
            // `let : Algebra B S := …` names nothing, relying on the type alone.
            let_lhs.clone().or_not(),
            type_spec(g).or_not(),
            let_value,
            tok(SEMICOLON).or_not(),
            term.clone(),
        )),
    ));

    let have_term = with_position(node(
        HAVE_TERM,
        group((
            // mathlib's `haveI`/`letI` introduce instances and are ordinary
            // identifiers, not keywords, but take the same shape.
            choice((tok(KW_HAVE), ident_named(&["haveI", "letI"]))),
            let_lhs.clone().or_not(),
            type_spec(g).or_not(),
            tok(COLON_EQ),
            term.clone(),
            tok(SEMICOLON).or_not(),
            term.clone(),
        )),
    ));

    let by_term = node(BY_TERM, group((tok(KW_BY), g.tactic_seq.clone())));

    // `show T from e` and `show T by tac` are both proofs of the restatement.
    let show_term = with_position(node(
        SHOW_TERM,
        group((
            tok(KW_SHOW),
            term.clone(),
            choice((
                group((tok(KW_FROM), term.clone()))
                    .map(|(kw, t)| Frag::Node(DECL_BODY, vec![kw, t])),
                by_term.clone(),
            ))
            .or_not(),
        )),
    ));

    let suffices_term = with_position(node(
        SUFFICES_TERM,
        group((
            tok(KW_SUFFICES),
            let_lhs.clone().or_not(),
            type_spec(g).or_not(),
            choice((
                group((tok(KW_FROM), term.clone()))
                    .map(|(kw, t)| Frag::Node(DECL_BODY, vec![kw, t])),
                by_term.clone(),
            ))
            .or_not(),
        )),
    ));

    // `match h : e, e' with | …`
    let discr = group((group((tok(IDENT), tok(COLON))).or_not(), term.clone())).map(|(h, t)| {
        let mut kids = Vec::new();
        h.push_kids(&mut kids);
        kids.push(t);
        Frag::Node(MATCH_DISCRS, kids)
    });

    let match_term = node(
        MATCH_TERM,
        group((
            tok(KW_MATCH),
            sep_list(discr, COMMA),
            tok(KW_WITH),
            match_alts(g),
        )),
    );

    let nomatch_term = node(MATCH_TERM, group((tok(KW_NOMATCH), term.clone())));

    let if_term = choice((
        // `if let .some x := e then … else …`
        node(
            IF_LET,
            group((
                tok(KW_IF),
                tok(KW_LET),
                term.clone(),
                tok(COLON_EQ),
                term.clone(),
                tok(KW_THEN),
                term.clone(),
                tok(KW_ELSE),
                term.clone(),
            )),
        ),
        node(
            IF_TERM,
            group((
                tok(KW_IF),
                group((tok(IDENT), tok(COLON))).or_not(),
                term.clone(),
                tok(KW_THEN),
                term.clone(),
                tok(KW_ELSE),
                term.clone(),
            )),
        ),
    ));

    let do_term = node(DO_TERM, group((tok(KW_DO), g.do_seq.clone())));
    // Kept for use as a trailing application argument, below.
    let trailing_do_arg = do_term.clone();

    // `calc a = b := pf` followed by `_ = c := pf` steps.
    let calc_step = node(
        CALC_STEP,
        group((term.clone(), tok(COLON_EQ), term.clone())),
    );
    let calc_term = node(
        CALC_TERM,
        group((
            tok(KW_CALC),
            layout_block(MATCH_ALTS, calc_step, &[], false),
        )),
    );

    // A syntax quotation `` `(…) ``; its contents are kept but not interpreted.
    let quoted = node(
        QUOTED_TERM,
        group((
            tok_in(&[BACKTICK, DOUBLE_BACKTICK]),
            tok(L_PAREN),
            balanced_run(RAW_TOKENS, |_| false, true),
            tok(R_PAREN),
        )),
    );

    // Order matters: rules with a distinguishing prefix come first, and
    // `dep_arrow` precedes `paren` so `(x : α) → β` is not read as an
    // ascription followed by a stray arrow.
    // Lean restricts application arguments to maximal precedence, so the
    // "big" terms below are *not* bare arguments — which is exactly what keeps
    // `for i in xs do …` from reading `do …` as an argument of `xs`.
    let big = choice((
        fun_term.clone(),
        quantifier,
        let_term,
        have_term,
        show_term,
        suffices_term,
        match_term,
        nomatch_term,
        if_term,
        do_term,
        by_term,
        calc_term,
    ))
    .boxed();

    // Terms that may appear anywhere, including as an application argument.
    let small = choice((
        literal,
        sort,
        sorry,
        quoted,
        paren,
        notation_bracket,
        abs_value,
        anon_ctor,
        array_lit,
        vec_lit,
        card_term,
        list_lit,
        brace,
        anon_have,
        at_term,
        antiquotation,
        synthetic_hole,
        dot_ident,
        cdot,
        hole,
        ellipsis,
        coerced,
        reference,
        constant_term,
    ))
    .boxed();

    // `dep_arrow` must precede `paren` so `(x : α) → β` is read as a dependent
    // arrow rather than an ascription followed by a stray arrow. It is a head
    // position only: in `f (x : α) → β` the parenthesised part is an argument.
    let atom_head = choice((big, dep_arrow, small.clone(), symbol_term)).boxed();

    // ---- Trailers ----------------------------------------------------------

    // Each trailer yields the node kind to build and the tokens after the
    // receiver, so the fold can splice the receiver in as the first child.
    let trailer = choice((
        // `ℤˣ`, `sᶜ`, `x⁻¹`, `Kᗮ` — postfix notation binds tighter than
        // application, so it attaches to the argument rather than to the whole
        // application. The operator-table entries cover the same forms applied
        // to a complete term.
        tok_in(&[MODIFIER, INV]).map(|m| (POSTFIX_TERM, vec![m])),
        adjacent_tok(SYMBOL).map(|m| (POSTFIX_TERM, vec![m])),
        group((adjacent_tok(DOT), tok(NUMBER))).map(|(d, n)| (PROJ, vec![d, n])),
        group((adjacent_tok(DOT), ident())).map(|(d, n)| (FIELD_ACCESS, vec![d, n])),
        // Universe arguments: `Foo.{u, v}`.
        // Universe arguments: `Foo.{u, v}`, and also `Foo.{max u w}`, since a
        // level is an expression rather than only a name.
        group((
            adjacent_tok(DOT),
            tok(L_BRACE),
            sep_list(term.clone(), COMMA),
            tok(R_BRACE),
        ))
        .map(|(d, l, levels, r)| {
            let mut kids = vec![d, l];
            kids.extend(levels);
            kids.push(r);
            (UNIV_ARGS, kids)
        }),
        group((tok(PIPE_RIGHT_DOT), tok_in(&[IDENT, NUMBER])))
            .map(|(p, n)| (PIPE_PROJ, vec![p, n])),
        // `R⟦X⟧` — power series over `R`. The same delimiters appear as a
        // standalone quotient class, so adjacency is what marks this use.
        group((
            adjacent_tok(L_DOUBLE_BRACKET),
            sep_list(term.clone(), COMMA).or_not(),
            tok(R_DOUBLE_BRACKET),
        ))
        .map(|(l, items, r)| {
            let mut kids = vec![l];
            kids.extend(items.into_iter().flatten());
            kids.push(r);
            (INDEX, kids)
        }),
        // `xs[i]`, `xs[i]?`, `xs[i]!`. Adjacency separates indexing from passing
        // a list as an argument, as in `f [a, b]` — the same distinction Lean
        // draws.
        group((
            adjacent_tok(L_BRACKET),
            sep_list(term.clone(), COMMA).or_not(),
            tok(R_BRACKET),
            // `xs[i]?`, `xs[i]!`, and `xs[i]'h` which supplies the in-bounds
            // proof directly.
            choice((
                tok_in(&[QUESTION, BANG]).map(|t| vec![t]),
                group((tok(TICK), term.clone())).map(|(t, p)| vec![t, p]),
            ))
            .or_not(),
        ))
        .map(|(l, items, r, marker)| {
            let mut kids = vec![l];
            kids.extend(items.into_iter().flatten());
            kids.push(r);
            kids.extend(marker.into_iter().flatten());
            (INDEX, kids)
        }),
    ));

    fn splice(receiver: Frag, (kind, rest): (SyntaxKind, Vec<Frag>)) -> Frag {
        let mut kids = vec![receiver];
        kids.extend(rest);
        Frag::Node(kind, kids)
    }

    let trailed_head = atom_head.foldl(trailer.clone().repeated(), splice).boxed();
    let trailed_arg = small.foldl(trailer.repeated(), splice).boxed();

    // ---- Application -------------------------------------------------------

    // Arguments must be indented past the enclosing position, so a dedented
    // line starts new syntax instead of becoming an argument.
    let app = trailed_head
        .then(
            col_gt()
                .ignore_then(trailed_arg)
                .repeated()
                .collect::<Vec<_>>(),
        )
        // Lean's concessions to big terms in argument position: a trailing
        // lambda, as in `xs.map fun x => x + 1`, and a trailing `do` block, as
        // in `withSavedScopeOverride do …`.
        //
        // The `do` form needs a guard, because `for x in xs do …` is not an
        // application of `xs` to a `do` block. The context carries whether one
        // is permitted, and a loop's collection is parsed with it off.
        .then(
            col_gt()
                .ignore_then(choice((
                    fun_term,
                    trailing_do_allowed().ignore_then(trailing_do_arg),
                )))
                .or_not(),
        )
        .map(|((head, mut args), trailing)| {
            args.extend(trailing);
            if args.is_empty() {
                head
            } else {
                let mut kids = vec![head];
                kids.extend(args);
                Frag::Node(APP, kids)
            }
        })
        .boxed();

    // ---- Operator table ----------------------------------------------------

    // Precedences follow Lean's own notation declarations.
    let infixes = vec![
        infix(right(20), tok_in(&[ALTERNATIVE]), mk_infix),
        infix(right(20), tok_in(&[IFF, IFF_ASCII]), mk_infix),
        infix(right(30), tok_in(&[OR, OR_OR, OPLUS]), mk_infix),
        infix(right(35), tok_in(&[AND, AND_AND, TIMES]), mk_infix),
        infix(
            left(50),
            tok_in(&[
                EQ, EQ_EQ, NE, NE_ASCII, LT, GT, LE, GE, LE_ASCII, GE_ASCII, MEM, NOT_MEM,
                SUBSET_EQ, SUBSET, DVD, HEQ, EQUIV,
            ]),
            mk_infix,
        ),
        infix(left(55), tok_in(&[BIND]), mk_infix),
        infix(left(60), tok_in(&[SEQ_RIGHT, SEQ_AP]), mk_infix),
        infix(left(65), tok_in(&[PLUS, MINUS, UNION, SUP]), mk_infix),
        infix(right(65), tok_in(&[PLUS_PLUS]), mk_infix),
        infix(right(67), tok_in(&[DOUBLE_COLON]), mk_infix),
        infix(
            left(70),
            tok_in(&[STAR, SLASH, PERCENT, INTER, INF, BACKSLASH]),
            mk_infix,
        ),
        infix(right(75), tok_in(&[CARET]), mk_infix),
        infix(right(90), tok_in(&[COMPOSE]), mk_infix),
        // Curated from the mathlib census, with Lean's own precedences.
        infix(right(80), tok_in(&[GG, GGG, ISO_TRANS]), mk_infix),
        infix(left(50), tok_in(&[LL]), mk_infix),
        // `f  s` is Set.image, infixl:80 in mathlib.
        infix(left(80), tok_in(&[IMAGE]), mk_infix),
        infix(right(73), tok_in(&[BULLET]), mk_infix),
        infix(right(26), tok_in(&[FUNCTOR_ARROW]), mk_infix),
        infix(right(10), tok_in(&[LONG_ARROW]), mk_infix),
        infix(left(50), tok_in(&[CONGR_MOD, TILDE]), mk_infix),
        infix(left(35), tok_in(&[QUOTIENT]), mk_infix),
        infix(left(60), tok_in(&[DOT_DOT]), mk_infix),
        infix(right(100), tok_in(&[MAP]), mk_infix),
        // `f <| x` and `x |> f` are the low-precedence application pipes.
        infix(right(2), tok_in(&[PIPE_LEFT, DOLLAR]), mk_infix),
        infix(left(1), tok_in(&[PIPE_RIGHT]), mk_infix),
    ];

    // `→` is right-associative and binds looser than every relation, so
    // `a = b → c = d` groups as `(a = b) → (c = d)`.
    let arrows = vec![infix(right(25), tok_in(&[ARROW, THIN_ARROW]), mk_arrow)];

    let prefixes = vec![
        prefix(40, tok_in(&[NOT]), mk_prefix),
        prefix(75, tok_in(&[MINUS, BANG]), mk_prefix),
        // `↑x`, `⇑f`, `↥S` bind tighter than any operator.
        prefix(1000, tok_in(&[UP_ARROW, COE_FUN, COE_SORT]), mk_prefix),
        // `← e` inside `do`; harmless elsewhere.
        prefix(1, tok_in(&[LEFT_ARROW, LEFT_ARROW_ASCII]), mk_prefix),
    ];

    // Modifier runs are postfix at maximal precedence: `sᶜ`, `Xᵒᵖ`, `‖x‖₊`.
    // `(card α - 1)!` and `n !` — factorial. A `!` directly after an identifier
    // is part of that identifier, so this only applies after a bracket or across
    // whitespace, and never competes with `!b` for boolean negation, which the
    // prefix entry takes at the head of a term.
    let postfixes = vec![postfix(1000, tok_in(&[INV, MODIFIER, BANG]), mk_postfix)];

    // Operators that may carry a bracketed parameter. `⊗` gets Lean's
    // precedence; `SYMBOL` — every notation character without a rule of its
    // own — gets an *assumed* one, which is why the operator keeps the `SYMBOL`
    // token kind: a consumer can tell a known precedence from a guessed one.
    let bracket_params = node(
        ARG_LIST,
        group((
            tok(L_BRACKET),
            sep_list(term.clone(), COMMA).or_not(),
            tok(R_BRACKET),
        )),
    )
    .boxed();
    // A generic symbol written flush against its operand is postfix notation:
    // `Kᗮ` is an orthogonal complement, `A†` an adjoint. Adjacency is what
    // separates these from infix use, since Lean style puts spaces around
    // binary operators and none before a postfix modifier. Tried before the
    // generic infix entry below.
    let adjacent_postfix = vec![postfix(1000, adjacent_tok(SYMBOL), mk_postfix)];

    let parameterized = vec![
        infix(
            left(70),
            param_op(&[OTIMES], bracket_params.clone()),
            mk_infix,
        ),
        infix(left(65), param_op(&[SYMBOL], bracket_params), mk_infix),
    ];

    app.pratt((
        infixes,
        arrows,
        prefixes,
        postfixes,
        adjacent_postfix,
        parameterized,
    ))
    .boxed()
}

/// A `do` block's statement sequence.
pub fn do_seq<'a>(g: &Grammar<'a>) -> BoxedP<'a, Frag> {
    let term = g.term.clone();

    let let_lhs = choice((
        group((tok_in(&[IDENT, UNDERSCORE]), binders_opt(g)))
            .map(|(n, b)| Frag::Node(DECL_ID, vec![n, b])),
        node(
            ANON_CTOR,
            group((
                tok(L_ANGLE_ANON),
                sep_list(term.clone(), COMMA).or_not(),
                tok(R_ANGLE_ANON),
            )),
        ),
    ));

    let item = choice((
        // `let x ← e` and `let mut x := e`
        node(
            DO_LET_ARROW,
            group((
                tok(KW_LET),
                tok(KW_MUT).or_not(),
                let_lhs.clone(),
                type_spec(g).or_not(),
                tok_in(&[LEFT_ARROW, LEFT_ARROW_ASCII]),
                term.clone(),
            )),
        ),
        node(
            DO_LET,
            group((
                tok(KW_LET),
                tok(KW_MUT).or_not(),
                let_lhs.clone(),
                type_spec(g).or_not(),
                tok(COLON_EQ),
                term.clone(),
            )),
        ),
        // `x ← e`
        node(
            DO_BIND,
            group((
                let_lhs.clone(),
                tok_in(&[LEFT_ARROW, LEFT_ARROW_ASCII]),
                term.clone(),
            )),
        ),
        // `x := e` — reassignment of a `mut` binding.
        node(
            DO_REASSIGN,
            group((tok(IDENT), tok(COLON_EQ), term.clone())),
        ),
        node(DO_RETURN, group((tok(KW_RETURN), term.clone().or_not()))),
        node(DO_BREAK, tok(KW_BREAK)),
        node(DO_CONTINUE, tok(KW_CONTINUE)),
        node(
            DO_FOR,
            group((
                tok(KW_FOR),
                sep_list(
                    group((term.clone(), tok(KW_IN), without_trailing_do(term.clone())))
                        .map(|(p, i, e)| Frag::Node(BINDERS, vec![p, i, e])),
                    COMMA,
                ),
                tok(KW_DO),
                g.do_seq.clone(),
            )),
        ),
        node(
            DO_WHILE,
            group((
                tok(KW_WHILE),
                without_trailing_do(term.clone()),
                tok(KW_DO),
                g.do_seq.clone(),
            )),
        ),
        node(DO_REPEAT, group((tok(KW_REPEAT), g.do_seq.clone()))),
        // In `do`, the `else` branch is optional.
        node(
            DO_IF,
            group((
                tok(KW_IF),
                group((tok(IDENT), tok(COLON))).or_not(),
                term.clone(),
                tok(KW_THEN),
                g.do_seq.clone(),
                group((tok(KW_ELSE), g.do_seq.clone())).or_not(),
            )),
        ),
        // `try … catch e => … finally …`
        node(
            DO_TRY,
            group((
                tok(KW_TRY),
                g.do_seq.clone(),
                node(
                    DO_CATCH,
                    group((
                        tok(KW_CATCH),
                        choice((
                            group((term.clone(), tok(FAT_ARROW)))
                                .map(|(t, a)| Frag::Node(PATTERNS, vec![t, a])),
                            node(MATCH_ALTS, tok(FAT_ARROW)),
                        )),
                        g.do_seq.clone(),
                    )),
                )
                .repeated()
                .collect::<Vec<_>>(),
                node(DO_FINALLY, group((tok(KW_FINALLY), g.do_seq.clone()))).or_not(),
            )),
        ),
        node(
            DO_UNLESS,
            group((
                tok(KW_UNLESS),
                without_trailing_do(term.clone()),
                tok(KW_DO),
                g.do_seq.clone(),
            )),
        ),
        node(DO_EXPR, term.clone()),
    ));

    layout_block(DO_SEQ, item, &[SEMICOLON], true).boxed()
}
