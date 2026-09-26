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
    let synthetic_hole = node(SYNTHETIC_HOLE, group((tok(QUESTION), tok_in(&[IDENT]))));
    let sorry = node(SORRY_TERM, tok(KW_SORRY));
    let cdot = node(CDOT_TERM, tok_in(&[CDOT, BULLET]));
    // `.mk`, `.none` — constructor names resolved from the expected type.
    let dot_ident = node(DOT_IDENT, group((tok(DOT), ident())));
    let at_term = node(AT_TERM, group((tok(AT), tok_in(&[IDENT, UNDERSCORE]))));

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
        node(
            TYPE_ASCRIPTION,
            group((
                tok(L_PAREN),
                term.clone(),
                tok(COLON),
                term.clone(),
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
        node(
            PAREN_TERM,
            group((tok(L_PAREN), term.clone(), tok(R_PAREN))),
        ),
    ));

    let anon_ctor = node(
        ANON_CTOR,
        group((
            tok(L_ANGLE_ANON),
            comma_terms.clone().or_not(),
            tok(R_ANGLE_ANON),
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
                node(STRUCT_INST_SRC, group((term.clone(), tok(KW_WITH)))),
                sep_list(struct_field.clone(), COMMA).or_not(),
                tok(R_BRACE),
            )),
        ),
        // `{ x := 1, y := 2 }`
        node(
            STRUCT_INST,
            group((
                tok(L_BRACE),
                sep_list(
                    node(
                        STRUCT_INST_FIELD,
                        group((tok(IDENT), tok(COLON_EQ), term.clone())),
                    ),
                    COMMA,
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

    // `∃ x > 0, p x` — the relation is sugar for a conjunction.
    let binder_pred = group((
        tok_in(&[
            LT, GT, LE, GE, LE_ASCII, GE_ASCII, NE, MEM, NOT_MEM, SUBSET_EQ, EQ,
        ]),
        term.clone(),
    ));

    let quantifier = node(
        QUANTIFIER,
        group((
            tok_in(&[FORALL, KW_FORALL_KW, EXISTS, KW_EXISTS_KW, SIGMA, PI]),
            binders(g),
            type_spec(g).or_not(),
            binder_pred.or_not(),
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

    let let_term = node(
        LET_TERM,
        group((
            tok(KW_LET),
            tok(KW_REC).or_not(),
            let_lhs.clone(),
            type_spec(g).or_not(),
            let_value,
            tok(SEMICOLON).or_not(),
            term.clone(),
        )),
    );

    let have_term = node(
        HAVE_TERM,
        group((
            tok(KW_HAVE),
            let_lhs.clone().or_not(),
            type_spec(g).or_not(),
            tok(COLON_EQ),
            term.clone(),
            tok(SEMICOLON).or_not(),
            term.clone(),
        )),
    );

    let show_term = node(
        SHOW_TERM,
        group((
            tok(KW_SHOW),
            term.clone(),
            group((tok(KW_FROM), term.clone())).or_not(),
        )),
    );

    let suffices_term = node(
        SUFFICES_TERM,
        group((
            tok(KW_SUFFICES),
            let_lhs.clone().or_not(),
            type_spec(g).or_not(),
            group((tok(KW_FROM), term.clone())).or_not(),
        )),
    );

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

    let by_term = node(BY_TERM, group((tok(KW_BY), g.tactic_seq.clone())));
    let do_term = node(DO_TERM, group((tok(KW_DO), g.do_seq.clone())));

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
        anon_ctor,
        list_lit,
        brace,
        anon_have,
        at_term,
        synthetic_hole,
        dot_ident,
        cdot,
        hole,
        reference,
    ))
    .boxed();

    // `dep_arrow` must precede `paren` so `(x : α) → β` is read as a dependent
    // arrow rather than an ascription followed by a stray arrow. It is a head
    // position only: in `f (x : α) → β` the parenthesised part is an argument.
    let atom_head = choice((big, dep_arrow, small.clone())).boxed();

    // ---- Trailers ----------------------------------------------------------

    // Each trailer yields the node kind to build and the tokens after the
    // receiver, so the fold can splice the receiver in as the first child.
    let trailer = choice((
        group((adjacent_tok(DOT), tok(NUMBER))).map(|(d, n)| (PROJ, vec![d, n])),
        group((adjacent_tok(DOT), ident())).map(|(d, n)| (FIELD_ACCESS, vec![d, n])),
        // Universe arguments: `Foo.{u, v}`.
        group((
            adjacent_tok(DOT),
            tok(L_BRACE),
            sep_list(tok_in(&[IDENT, NUMBER, UNDERSCORE]), COMMA),
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
        // Lean's one concession to big terms in argument position: a trailing
        // lambda, as in `xs.map fun x => x + 1`.
        .then(col_gt().ignore_then(fun_term).or_not())
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
            tok_in(&[STAR, SLASH, PERCENT, INTER, INF]),
            mk_infix,
        ),
        infix(right(75), tok_in(&[CARET]), mk_infix),
        infix(right(90), tok_in(&[COMPOSE]), mk_infix),
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
        // `← e` inside `do`; harmless elsewhere.
        prefix(1, tok_in(&[LEFT_ARROW, LEFT_ARROW_ASCII]), mk_prefix),
    ];

    let postfixes = vec![postfix(1000, tok_in(&[INV]), mk_postfix)];

    app.pratt((infixes, arrows, prefixes, postfixes)).boxed()
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
                    group((term.clone(), tok(KW_IN), term.clone()))
                        .map(|(p, i, e)| Frag::Node(BINDERS, vec![p, i, e])),
                    COMMA,
                ),
                tok(KW_DO),
                g.do_seq.clone(),
            )),
        ),
        node(
            DO_WHILE,
            group((tok(KW_WHILE), term.clone(), tok(KW_DO), g.do_seq.clone())),
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
            group((tok(KW_UNLESS), term.clone(), tok(KW_DO), g.do_seq.clone())),
        ),
        node(DO_EXPR, term.clone()),
    ));

    layout_block(DO_SEQ, item, &[SEMICOLON], true).boxed()
}
