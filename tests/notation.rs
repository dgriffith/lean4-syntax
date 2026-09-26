//! Notation support: a curated table for the head of mathlib's distribution,
//! and a generic fallback for its tail.
//!
//! The split matters. Curated operators get Lean's real precedence; everything
//! else gets an *assumed* one, and the tree says which is which — the operator
//! keeps the `SYMBOL` token kind, so a consumer reasoning about associativity
//! can tell a known precedence from a guess.

use lean4_syntax::SyntaxKind::*;
use lean4_syntax::ast::{AstNode, Command, HasDecl, SourceFile};
use lean4_syntax::syntax::sexpr;

/// The shape of a definition's body.
fn body(src: &str) -> String {
    let text = format!("def f := {src}");
    let parse = lean4_syntax::parse(&text);
    assert!(
        parse.ok(),
        "unexpected errors parsing {src:?}: {:?}",
        parse.errors()
    );
    let file = SourceFile::cast(parse.syntax()).unwrap();
    let Some(Command::Def(def)) = file.commands().next() else {
        panic!("expected a def, got:\n{}", sexpr(&parse.syntax()))
    };
    sexpr(def.value().expect("a value").syntax())
}

/// Asserts a snippet parses cleanly as a whole file.
fn clean(src: &str) {
    let parse = lean4_syntax::parse(src);
    assert!(
        parse.ok(),
        "unexpected errors in {src:?}: {:?}",
        parse.errors()
    );
}

// ---- The generic fallback --------------------------------------------------

#[test]
fn an_unknown_notation_character_is_an_atom() {
    // mathlib uses 292 characters with no rule of their own. They must parse.
    assert_eq!(body("⊤"), "(SYMBOL_TERM ⊤)");
    assert_eq!(body("∞"), "(SYMBOL_TERM ∞)");
    assert_eq!(body("𝟙 X"), "(APP (SYMBOL_TERM 𝟙) (REF X))");
}

#[test]
fn an_unknown_notation_character_is_an_infix_operator() {
    // `⊸` has no rule; it still parses, at an assumed precedence.
    assert_eq!(body("a ⊸ b"), "(INFIX_TERM (REF a) (OPERATOR ⊸) (REF b))");
}

#[test]
fn an_assumed_precedence_is_visible_in_the_tree() {
    // The operator keeps the SYMBOL kind, which is how a consumer tells a
    // guessed precedence from one taken from Lean.
    let parse = lean4_syntax::parse("def f := a ⊸ b");
    let op = parse
        .syntax()
        .descendants()
        .find(|n| n.kind() == OPERATOR)
        .expect("a generic operator node");
    let token = op
        .children_with_tokens()
        .filter_map(|it| it.into_token())
        .find(|t| !t.kind().is_trivia())
        .unwrap();
    assert_eq!(
        token.kind(),
        SYMBOL,
        "assumed precedence must be detectable"
    );

    // A curated operator does not carry SYMBOL, so the two are distinguishable.
    let curated = lean4_syntax::parse("def f := a ≫ b");
    assert!(
        curated
            .syntax()
            .descendants_with_tokens()
            .filter_map(|it| it.into_token())
            .all(|t| t.kind() != SYMBOL),
        "`≫` has a real precedence and should not lex as a generic symbol"
    );
}

#[test]
fn modifier_runs_are_postfix() {
    assert_eq!(body("sᶜ"), "(POSTFIX_TERM (REF s) ᶜ)");
    assert_eq!(body("Xᵒᵖ"), "(POSTFIX_TERM (REF X) ᵒᵖ)");
    // Chained onto a bracketed form: `‖x‖₊`.
    assert_eq!(
        body("‖x‖₊"),
        "(POSTFIX_TERM (NOTATION_BRACKET ‖ (REF x) ‖) ₊)"
    );
}

#[test]
fn operators_may_carry_a_bracketed_parameter() {
    // mathlib's bundled-morphism arrows: `M →ₗ[R] N`, `M ⊗[R] N`.
    assert_eq!(
        body("M →ₗ[R] N"),
        "(INFIX_TERM (REF M) (OPERATOR →ₗ (ARG_LIST [ (REF R) ])) (REF N))"
    );
    clean("def f := M ⊗[R] N\n");
    clean("def f : (Nat → Nat) →+ Nat := g\n");
}

// ---- Curated notation ------------------------------------------------------

#[test]
fn delimiter_pairs_are_curated_because_they_cannot_be_generic() {
    // `‖` is the same character at both ends, so no generic rule can pair it.
    assert_eq!(body("‖x‖"), "(NOTATION_BRACKET ‖ (REF x) ‖)");
    assert_eq!(body("⌊x⌋"), "(NOTATION_BRACKET ⌊ (REF x) ⌋)");
    assert_eq!(body("⌈x⌉"), "(NOTATION_BRACKET ⌈ (REF x) ⌉)");
    clean("def f := ⟪x, y⟫\n");
    // Lie bracket, from General Punctuation rather than a mathematical block.
    clean("def f := ⁅x, y⁆\n");
}

#[test]
fn curated_operators_use_leans_precedence() {
    // `≫` is infixr:80, so it groups to the right.
    assert_eq!(
        body("f ≫ g ≫ h"),
        "(INFIX_TERM (REF f) ≫ (INFIX_TERM (REF g) ≫ (REF h)))"
    );
    // `⟶` is infixr:10, looser than `≫`.
    assert_eq!(
        body("X ⟶ Y ≫ Z"),
        "(INFIX_TERM (REF X) ⟶ (INFIX_TERM (REF Y) ≫ (REF Z)))"
    );
    // `•` is scalar multiplication at 73, binding tighter than `+` at 65.
    assert_eq!(
        body("a • b + c"),
        "(INFIX_TERM (INFIX_TERM (REF a) • (REF b)) + (REF c))"
    );
}

#[test]
fn big_operators_bind_variables() {
    // These have the shape of a quantifier, not of an operator.
    assert_eq!(
        body("∑ i, f i"),
        "(QUANTIFIER ∑ (BINDERS (SIMPLE_BINDER i)) , (APP (REF f) (REF i)))"
    );
    for src in [
        "def f := ∑ i ∈ s, g i\n",
        "def f := ∏ i ∈ s, g i\n",
        "def f := ⨆ i, g i\n",
        "def f := ⋃ i, g i\n",
        "def f := ∫ x, g x\n",
        "def f := ∫ x in a..b, g x\n",
    ] {
        clean(src);
    }
}

#[test]
fn image_is_an_operator_not_two_character_literals() {
    assert_eq!(body("f '' s"), "(INFIX_TERM (REF f) '' (REF s))");
    // A real character literal still lexes as one.
    assert_eq!(body("'x'"), "(LITERAL 'x')");
}

#[test]
fn decorated_type_names_are_single_identifiers() {
    // `ℕ+` is `PNat`, a token in Lean rather than `ℕ` plus `+`.
    assert_eq!(body("ℕ+"), "(REF ℕ+)");
    clean("def f (n : ℕ+) : ℕ+ := n\n");
    clean("def f (x : ℝ≥0∞) : ℝ≥0 := y\n");
    // Ordinary arithmetic is untouched.
    assert_eq!(body("a+b"), "(INFIX_TERM (REF a) + (REF b))");
}

// ---- Core syntax the notation work exposed --------------------------------

#[test]
fn named_arguments_are_distinct_from_ascriptions() {
    assert_eq!(
        body("g (p := e)"),
        "(APP (REF g) (NAMED_ARG ( p := (REF e) )))"
    );
    // `(e : T)` still ascribes, since `:` and `:=` are different tokens.
    assert_eq!(
        body("(x : Nat)"),
        "(TYPE_ASCRIPTION ( (REF x) : (REF Nat) ))"
    );
}

#[test]
fn antiquotations_splice_into_macros() {
    assert_eq!(
        body("congr($ha + $hb)"),
        "(APP (REF congr) (PAREN_TERM ( (INFIX_TERM (ANTIQUOTATION $ ha) + (ANTIQUOTATION $ hb)) )))"
    );
}

#[test]
fn scope_modifiers_precede_unrecognised_commands() {
    // mathlib's `notation3`, which this parser does not model.
    clean("scoped notation3 \"x\" => y\n");
    clean("local notation3 \"x\" => y\n");
}

#[test]
fn attribute_commands_take_an_in_clause() {
    clean("attribute [local simp] map_ofNat in\ntheorem t : True := trivial\n");
}

// ---- Regression ------------------------------------------------------------

#[test]
fn a_bullet_is_scalar_multiplication_not_a_focus_dot() {
    // `•` was wrongly treated as a tactic focus dot. Lean focuses with `·`.
    let parse = lean4_syntax::parse("theorem t : True := by\n  refine ?_\n  · trivial\n");
    assert!(parse.ok(), "{:?}", parse.errors());
    assert_eq!(
        parse
            .syntax()
            .descendants()
            .filter(|n| n.kind() == TACTIC_FOCUS)
            .count(),
        1
    );
    // And `•` still parses as an operator in a term.
    clean("def f (r : Nat) (x : Nat) := r • x\n");
}
