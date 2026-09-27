//! The command grammar: everything that can appear at the top level of a file.
//!
//! Declarations (`def`, `theorem`, `structure`, `inductive`, …) are fully
//! structured. Commands that *extend the grammar* — `notation`, `syntax`,
//! `macro_rules` — are recognised and their bodies retained as token runs
//! rather than interpreted, which is the boundary of the chosen scope: the file
//! still round-trips and the declaration is still visible in the tree, but the
//! new notation does not become available to the term parser.

use super::Grammar;
use super::support::*;
use super::term::{binders_opt, bracket_binder, match_alts, type_spec};
use crate::kind::SyntaxKind::{self, *};
use crate::syntax::Frag;
use chumsky::prelude::*;

/// True if this token can begin a top-level command.
///
/// Used by error recovery to find the next place worth resuming from.
pub fn is_command_start(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        KW_IMPORT
            | KW_MODULE
            | KW_PUBLIC
            | KW_META
            | KW_PRELUDE
            | KW_OPEN
            | KW_EXPORT
            | KW_INCLUDE
            | KW_OMIT
            | KW_NONREC
            | KW_NAMESPACE
            | KW_SECTION
            | KW_END
            | KW_VARIABLE
            | KW_VARIABLES
            | KW_UNIVERSE
            | KW_SET_OPTION
            | KW_ATTRIBUTE
            | KW_DEF
            | KW_THEOREM
            | KW_LEMMA
            | KW_ABBREV
            | KW_EXAMPLE
            | KW_INSTANCE
            | KW_AXIOM
            | KW_OPAQUE
            | KW_STRUCTURE
            | KW_CLASS
            | KW_INDUCTIVE
            | KW_MUTUAL
            | KW_NOTATION
            | KW_INFIX
            | KW_INFIXL
            | KW_INFIXR
            | KW_PREFIX
            | KW_POSTFIX
            | KW_MACRO
            | KW_MACRO_RULES
            | KW_SYNTAX
            | KW_ELAB
            | KW_ELAB_RULES
            | KW_DECLARE_SYNTAX_CAT
            | KW_INITIALIZE
            | KW_BUILTIN_INITIALIZE
            | KW_PRIVATE
            | KW_PROTECTED
            | KW_PARTIAL
            | KW_UNSAFE
            | KW_NONCOMPUTABLE
            | KW_LOCAL
            | KW_SCOPED
            | DOC_COMMENT
            | MOD_DOC_COMMENT
            | AT
            | HASH
    )
}

/// Stops a raw run at `in`, for the `open X in <command>` form.
fn stops_at_in(kind: SyntaxKind) -> bool {
    kind == KW_IN
}

/// Never stops; the run ends only at a dedent.
fn never(_: SyntaxKind) -> bool {
    false
}

/// Stops at a comma, for attribute lists.
fn stops_at_comma(kind: SyntaxKind) -> bool {
    kind == COMMA
}

/// The command parser.
pub fn command<'a>(g: &Grammar<'a>) -> BoxedP<'a, Frag> {
    let term = g.term.clone();
    let cmd = g.command.clone();

    // ---- Declaration prologue ---------------------------------------------

    // `@[simp, to_additive (attr := simp)]`
    let attr_list = node(
        ATTR_LIST,
        group((
            tok(AT),
            tok(L_BRACKET),
            sep_list(
                node(ATTR, bracketed_run(RAW_TOKENS, stops_at_comma, false)),
                COMMA,
            ),
            tok(R_BRACKET),
        )),
    );

    // `local`, `scoped`, and `scoped[Namespace]`, which scopes a notation to a
    // namespace other than the current one.
    let scope_modifier = group((
        tok_in(&[KW_LOCAL, KW_SCOPED]),
        group((tok(L_BRACKET), tok(IDENT), tok(R_BRACKET))).or_not(),
    ));

    let modifiers = node(
        DECL_MODIFIERS,
        group((
            tok(DOC_COMMENT).or_not(),
            attr_list.clone().or_not(),
            tok_in(&[
                KW_PRIVATE,
                KW_PROTECTED,
                KW_PUBLIC,
                KW_META,
                KW_NONCOMPUTABLE,
                KW_NONREC,
                KW_UNSAFE,
                KW_PARTIAL,
                KW_LOCAL,
                KW_SCOPED,
            ])
            .repeated()
            .collect::<Vec<_>>(),
        )),
    );

    // `foo.{u, v}`
    // `module` is a soft keyword: the module-system command at the top of a
    // file, and an ordinary name anywhere else — `instance module : Module R …`
    // is real mathlib. Reserving it outright was a regression introduced with
    // the module system.
    let decl_name = tok_in(&[IDENT, KW_MODULE]);

    let decl_id = node(
        DECL_ID,
        group((
            decl_name.clone(),
            group((
                adjacent_tok(DOT),
                tok(L_BRACE),
                sep_list(tok(IDENT), COMMA),
                tok(R_BRACE),
            ))
            .or_not(),
        )),
    );

    let decl_sig = node(DECL_SIG, group((binders_opt(g), type_spec(g).or_not())));

    let deriving = node(
        DERIVING_CLAUSE,
        group((tok(KW_DERIVING), sep_list(tok(IDENT), COMMA))),
    );

    // `where` in value position: `instance : Monad M where pure := …`
    let where_field = node(
        STRUCT_INST_FIELD,
        group((
            tok(IDENT),
            binders_opt(g),
            type_spec(g).or_not(),
            tok(COLON_EQ),
            term.clone(),
        )),
    );

    // The right-hand side of a declaration, in its three forms.
    let decl_body = choice((
        node(DECL_BODY, group((tok(COLON_EQ), term.clone()))),
        node(
            DECL_BODY,
            group((
                tok(KW_WHERE),
                // `instance : (forget₂ A B).Braided where` introduces no fields:
                // the instance is satisfied entirely by defaults.
                layout_block(STRUCT_FIELD_LIST, where_field.clone(), &[], true).or_not(),
            )),
        ),
        // Pattern-matching equations: `def f : Nat → Nat | 0 => 1 | n+1 => n`
        node(DECL_EQNS, match_alts(g)),
    ))
    .boxed();

    // `where` after a body, introducing auxiliary declarations.
    let where_decl = node(
        DEF,
        group((decl_id.clone(), decl_sig.clone(), decl_body.clone())),
    );
    let where_clause = node(
        WHERE_CLAUSE,
        group((
            tok(KW_WHERE),
            layout_block(WHERE_DECLS, where_decl, &[SEMICOLON], true),
        )),
    );

    // ---- Declarations ------------------------------------------------------

    let named_decl = |kw: &'static [SyntaxKind], kind: SyntaxKind| {
        node(
            kind,
            group((
                modifiers.clone(),
                tok_in(kw),
                decl_id.clone(),
                decl_sig.clone(),
                decl_body.clone().or_not(),
                where_clause.clone().or_not(),
                deriving.clone().or_not(),
            )),
        )
    };

    let def_decl = named_decl(&[KW_DEF], DEF);
    let theorem_decl = named_decl(&[KW_THEOREM, KW_LEMMA], THEOREM);
    let abbrev_decl = named_decl(&[KW_ABBREV], ABBREV);
    let axiom_decl = named_decl(&[KW_AXIOM], AXIOM);
    let opaque_decl = named_decl(&[KW_OPAQUE], OPAQUE_DECL);

    // `example` has no name; `instance` may omit one.
    let example_decl = node(
        EXAMPLE,
        group((
            modifiers.clone(),
            tok(KW_EXAMPLE),
            decl_sig.clone(),
            decl_body.clone(),
        )),
    );

    let instance_decl = node(
        INSTANCE,
        group((
            modifiers.clone(),
            tok(KW_INSTANCE),
            // An optional priority, `instance (priority := 100) …`.
            group((
                tok(L_PAREN),
                balanced_run(RAW_TOKENS, never, true),
                tok(R_PAREN),
            ))
            .or_not(),
            decl_id.clone().or_not(),
            decl_sig.clone(),
            decl_body.clone().or_not(),
            where_clause.clone().or_not(),
        )),
    );

    // ---- Structures, classes, inductives ----------------------------------

    let struct_field = node(
        STRUCT_FIELD,
        group((
            tok(DOC_COMMENT).or_not(),
            tok_in(&[KW_PRIVATE, KW_PROTECTED, KW_PUBLIC])
                .repeated()
                .collect::<Vec<_>>(),
            choice((
                bracket_binder(g),
                node(
                    SIMPLE_BINDER,
                    group((
                        tok(IDENT),
                        col_gt()
                            .ignore_then(tok(IDENT))
                            .repeated()
                            .collect::<Vec<_>>(),
                        // A field may take arguments: `G_le_6 (i) : #(G i) ≤ 6`
                        binders_opt(g),
                        type_spec(g),
                        group((tok(COLON_EQ), term.clone())).or_not(),
                    )),
                ),
            )),
        )),
    );

    let extends_clause = node(
        EXTENDS_CLAUSE,
        group((tok(KW_EXTENDS), sep_list(term.clone(), COMMA))),
    );

    // The docstring comes *before* the `|`:
    //
    // ```lean
    // inductive Reachable : (Fin 6 → ℕ) → Prop
    //   /-- The starting position -/
    //   | base : Reachable 1
    // ```
    let ctor = node(
        CTOR,
        group((
            tok(DOC_COMMENT).or_not(),
            tok(PIPE),
            tok(DOC_COMMENT).or_not(),
            tok_in(&[KW_PRIVATE, KW_PROTECTED, KW_PUBLIC])
                .repeated()
                .collect::<Vec<_>>(),
            tok(IDENT),
            binders_opt(g),
            type_spec(g).or_not(),
        )),
    );

    let structure_decl = node(
        STRUCTURE,
        group((
            modifiers.clone(),
            tok_in(&[KW_STRUCTURE]),
            decl_id.clone(),
            binders_opt(g),
            // `extends` may come before or after the result type; mathlib uses
            // both orders.
            choice((extends_clause.clone(), type_spec(g)))
                .repeated()
                .collect::<Vec<_>>(),
            group((
                tok(KW_WHERE),
                // The constructor may be named: `where mk ::`
                group((tok(IDENT), tok(DOUBLE_COLON))).or_not(),
                layout_block(STRUCT_FIELD_LIST, struct_field.clone(), &[], true).or_not(),
            ))
            .or_not(),
            deriving.clone().or_not(),
        )),
    );

    // `class inductive` declares constructors, not fields, so its body is an
    // `inductive` body. Tried before `class_decl`, whose body is a field list:
    // without this, `class inductive IsGCDMonoid … : Prop` parsed, then the
    // following `| intro : …` had nowhere to go.
    let class_inductive_decl = node(
        CLASS_DECL,
        group((
            modifiers.clone(),
            tok(KW_CLASS),
            tok(KW_INDUCTIVE),
            decl_id.clone(),
            binders_opt(g),
            type_spec(g).or_not(),
            tok(KW_WHERE).or_not(),
            layout_block(CTOR_LIST, ctor.clone(), &[], false).or_not(),
            deriving.clone().or_not(),
        )),
    );

    // A `class` is a structure, except that `class inductive` also exists.
    let class_decl = node(
        CLASS_DECL,
        group((
            modifiers.clone(),
            tok(KW_CLASS),
            tok(KW_INDUCTIVE).or_not(),
            decl_id.clone(),
            binders_opt(g),
            choice((extends_clause, type_spec(g)))
                .repeated()
                .collect::<Vec<_>>(),
            group((
                tok(KW_WHERE),
                group((tok(IDENT), tok(DOUBLE_COLON))).or_not(),
                layout_block(STRUCT_FIELD_LIST, struct_field, &[], true).or_not(),
            ))
            .or_not(),
            deriving.clone().or_not(),
        )),
    );

    let inductive_decl = node(
        INDUCTIVE,
        group((
            modifiers.clone(),
            tok(KW_INDUCTIVE),
            decl_id.clone(),
            binders_opt(g),
            type_spec(g).or_not(),
            tok(KW_WHERE).or_not(),
            layout_block(CTOR_LIST, ctor, &[], false).or_not(),
            deriving.clone().or_not(),
        )),
    );

    // ---- Plain commands ----------------------------------------------------

    let module_doc = node(MODULE_DOC, tok(MOD_DOC_COMMENT));

    // `module` marks the file as a module; `public import` and `meta import`
    // carry the visibility of the import.
    let module_cmd = node(MODULE_CMD, tok(KW_MODULE));

    let import = node(
        IMPORT,
        group((
            tok(KW_PRELUDE).or_not(),
            // `public meta import X` stacks two modifiers.
            tok_in(&[KW_PUBLIC, KW_PRIVATE, KW_META])
                .repeated()
                .collect::<Vec<_>>(),
            tok(KW_IMPORT),
            // The `col_gt` guard keeps an ident-led command on the next line
            // from being read as another module name: without it,
            // `import A.B` followed by `deprecated_module (…)` swallows the
            // command's name.
            col_gt()
                .ignore_then(tok(IDENT))
                .repeated()
                .at_least(1)
                .collect::<Vec<_>>(),
        )),
    );

    // `open Foo Bar (baz) in <command>`
    let open_cmd = node(
        OPEN_CMD,
        group((
            scope_modifier.clone().repeated().collect::<Vec<_>>(),
            tok(KW_OPEN),
            balanced_run(RAW_TOKENS, stops_at_in, false),
            group((tok(KW_IN), cmd.clone())).or_not(),
        )),
    );

    // `export Foo (bar baz)`, `include h`, `omit [Inst] h` — core commands that
    // mathlib uses heavily and that previously reached only the generic
    // fallback.
    let export_cmd = node(
        EXPORT_CMD,
        group((tok(KW_EXPORT), balanced_run(RAW_TOKENS, never, true))),
    );
    let include_cmd = node(
        INCLUDE_CMD,
        group((tok(KW_INCLUDE), balanced_run(RAW_TOKENS, never, true))),
    );
    let omit_cmd = node(
        OMIT_CMD,
        group((tok(KW_OMIT), balanced_run(RAW_TOKENS, never, true))),
    );

    let namespace = node(NAMESPACE, group((tok(KW_NAMESPACE), tok(IDENT))));
    let section = node(
        SECTION,
        group((
            attr_list.clone().or_not(),
            // `noncomputable section`, `@[expose] public noncomputable section`
            tok_in(&[KW_PUBLIC, KW_META, KW_NONCOMPUTABLE, KW_PRIVATE])
                .repeated()
                .collect::<Vec<_>>(),
            tok(KW_SECTION),
            tok(IDENT).or_not(),
        )),
    );
    let end_cmd = node(END_CMD, group((tok(KW_END), tok(IDENT).or_not())));

    let variable_cmd = node(
        VARIABLE_CMD,
        group((
            tok_in(&[KW_VARIABLE, KW_VARIABLES]),
            bracket_binder(g).repeated().at_least(1).collect::<Vec<_>>(),
            // `variable (M) in <command>` scopes the binders to one command.
            group((tok(KW_IN), cmd.clone())).or_not(),
        )),
    );

    let universe_cmd = node(
        UNIVERSE_CMD,
        group((
            tok(KW_UNIVERSE),
            col_gt()
                .ignore_then(tok(IDENT))
                .repeated()
                .at_least(1)
                .collect::<Vec<_>>(),
        )),
    );

    // `set_option trace.foo true in <command>`
    let set_option_cmd = node(
        SET_OPTION_CMD,
        group((
            tok(KW_SET_OPTION),
            tok(IDENT),
            balanced_run(RAW_TOKENS, stops_at_in, false),
            group((tok(KW_IN), cmd.clone())).or_not(),
        )),
    );

    let attribute_cmd = node(
        ATTRIBUTE_CMD,
        group((
            scope_modifier.clone().repeated().collect::<Vec<_>>(),
            tok(KW_ATTRIBUTE),
            tok(L_BRACKET),
            sep_list(
                node(ATTR, bracketed_run(RAW_TOKENS, stops_at_comma, false)),
                COMMA,
            ),
            tok(R_BRACKET),
            col_gt()
                .ignore_then(tok(IDENT))
                .repeated()
                .collect::<Vec<_>>(),
            group((tok(KW_IN), cmd.clone())).or_not(),
        )),
    );

    // `#check`, `#eval`, `#print`, …
    // `/-- info: 12 * 5 -/` then `#guard_msgs in` — a `#` command takes a
    // docstring, which is what `#guard_msgs` checks against.
    let hash_cmd = node(
        HASH_CMD,
        group((
            modifiers.clone(),
            tok(HASH),
            tok(IDENT).or_not(),
            balanced_run(RAW_TOKENS, never, true),
            group((tok(KW_IN), cmd.clone())).or_not(),
        )),
    );

    // ---- Grammar-extending commands (recorded, not applied) ----------------

    // `infixl:65 " ⊕ " => Sum`
    let precedence = node(PRECEDENCE, group((tok(COLON), tok(NUMBER))));

    let mixfix_cmd = node(
        MIXFIX_CMD,
        group((
            tok(DOC_COMMENT).or_not(),
            attr_list.clone().or_not(),
            scope_modifier.clone().repeated().collect::<Vec<_>>(),
            tok_in(&[KW_INFIX, KW_INFIXL, KW_INFIXR, KW_PREFIX, KW_POSTFIX]),
            precedence.clone().or_not(),
            attr_list.clone().or_not(),
            balanced_run(RAW_TOKENS, never, true),
        )),
    );

    let notation_cmd = node(
        NOTATION_CMD,
        group((
            tok(DOC_COMMENT).or_not(),
            attr_list.clone().or_not(),
            scope_modifier.clone().repeated().collect::<Vec<_>>(),
            tok(KW_NOTATION),
            precedence.or_not(),
            balanced_run(RAW_TOKENS, never, true),
        )),
    );

    // The remaining metaprogramming commands share a shape: a keyword followed
    // by syntax this parser deliberately does not interpret.
    let meta_cmd = |kw: &'static [SyntaxKind], kind: SyntaxKind| {
        node(
            kind,
            group((
                tok(DOC_COMMENT).or_not(),
                attr_list.clone().or_not(),
                scope_modifier.clone().repeated().collect::<Vec<_>>(),
                tok_in(kw),
                balanced_run(RAW_TOKENS, never, true),
            )),
        )
    };

    let syntax_cmd = meta_cmd(&[KW_SYNTAX], SYNTAX_CMD);
    let macro_rules_cmd = meta_cmd(&[KW_MACRO_RULES], MACRO_RULES_CMD);
    let macro_cmd = meta_cmd(&[KW_MACRO], MACRO_CMD);
    let elab_cmd = meta_cmd(&[KW_ELAB, KW_ELAB_RULES], ELAB_CMD);
    let syntax_cat_cmd = meta_cmd(&[KW_DECLARE_SYNTAX_CAT], DECLARE_SYNTAX_CAT_CMD);
    let initialize_cmd = meta_cmd(&[KW_INITIALIZE, KW_BUILTIN_INITIALIZE], INITIALIZE_CMD);

    // The negative lookahead matters: `end` is itself a command, so without it
    // the inner `repeated()` would consume the `end` that closes the block and
    // then fail at end of input.
    let mutual_block = node(
        MUTUAL_BLOCK,
        group((
            tok(KW_MUTUAL),
            tok(KW_END)
                .not()
                .ignore_then(cmd.clone())
                .repeated()
                .collect::<Vec<_>>(),
            tok(KW_END),
        )),
    );

    let declarations = choice((
        def_decl,
        theorem_decl,
        abbrev_decl,
        axiom_decl,
        opaque_decl,
        example_decl,
        instance_decl,
        structure_decl,
        class_inductive_decl,
        class_decl,
        inductive_decl,
    ))
    .boxed();

    let simple_commands = choice((
        module_doc,
        module_cmd,
        export_cmd,
        include_cmd,
        omit_cmd,
        import,
        open_cmd,
        namespace,
        section,
        end_cmd,
        variable_cmd,
        universe_cmd,
        set_option_cmd,
        attribute_cmd,
        hash_cmd,
        mutual_block,
    ))
    .boxed();

    let meta_commands = choice((
        mixfix_cmd,
        notation_cmd,
        syntax_cmd,
        macro_rules_cmd,
        macro_cmd,
        elab_cmd,
        syntax_cat_cmd,
        initialize_cmd,
    ))
    .boxed();

    // A command this parser does not know, such as mathlib's
    // `assert_not_exists Finset` or `alias foo := bar`. Mirrors the tactic
    // grammar's fallback: an unfamiliar command should not cascade into the
    // declarations after it. Requiring a leading identifier keeps it from
    // claiming the fragments left behind by a failed parse, which begin with
    // punctuation far more often.
    // Reusing `modifiers` lets an unrecognised command carry a docstring,
    // attributes and scope modifiers, which mathlib relies on:
    //
    // ```lean
    // @[deprecated (since := "2026-07-09")]
    // alias setOf_odd_degree_eq := setOfPred_odd_degree_eq
    // ```
    let unknown_cmd = node(
        UNKNOWN_CMD,
        group((
            modifiers.clone(),
            tok(IDENT),
            balanced_run(RAW_TOKENS, never, true),
        )),
    );

    // Declarations are tried first: they are the only forms that begin with
    // modifiers, and `@[…]` or `private` must not be mistaken for anything
    // else. The generic fallback is last.
    // mathlib writes a docstring ahead of commands that do not use one:
    //
    // ```lean
    // #adaptation_note
    // /-- `respectTransparency.types true` changes the signature -/
    // set_option backward.isDefEq.respectTransparency.types false in
    // ```
    //
    // Tried last, so a declaration still keeps its own docstring inside its
    // modifiers rather than being wrapped here.
    let documented = node(DOCUMENTED_CMD, group((tok(DOC_COMMENT), cmd.clone())));

    choice((
        declarations,
        simple_commands,
        meta_commands,
        unknown_cmd,
        documented,
    ))
    .boxed()
}
