//! Tree-shape tests: precedence, layout, and error recovery.

use lean4_syntax::ast::{AstNode, Command, HasDecl, SourceFile, TacticSeq};
use lean4_syntax::syntax::sexpr;

/// Parses `src` as the body of a definition and returns the body's shape.
///
/// Wrapping in a declaration keeps the tests focused on the term grammar while
/// still exercising the real top-level entry point.
fn term(src: &str) -> String {
    let text = format!("def f := {src}");
    let parse = lean4_syntax::parse(&text);
    assert!(
        parse.ok(),
        "unexpected errors parsing {src:?}: {:?}",
        parse.errors()
    );
    let file = SourceFile::cast(parse.syntax()).expect("root is a source file");
    let Some(Command::Def(def)) = file.commands().next() else {
        panic!("expected a def, got:\n{}", sexpr(&parse.syntax()))
    };
    sexpr(def.value().expect("def has a value").syntax())
}

/// Parses `src` and asserts it produced no errors, returning the whole shape.
fn shape(src: &str) -> String {
    let parse = lean4_syntax::parse(src);
    assert!(
        parse.ok(),
        "unexpected errors: {:?}\n{}",
        parse.errors(),
        lean4_syntax::syntax::debug_tree(&parse.syntax())
    );
    sexpr(&parse.syntax())
}

// ---- Precedence ------------------------------------------------------------

#[test]
fn multiplication_binds_tighter_than_addition() {
    assert_eq!(
        term("a + b * c"),
        "(INFIX_TERM (REF a) + (INFIX_TERM (REF b) * (REF c)))"
    );
    assert_eq!(
        term("a * b + c"),
        "(INFIX_TERM (INFIX_TERM (REF a) * (REF b)) + (REF c))"
    );
}

#[test]
fn subtraction_is_left_associative_and_power_is_right() {
    assert_eq!(
        term("a - b - c"),
        "(INFIX_TERM (INFIX_TERM (REF a) - (REF b)) - (REF c))"
    );
    assert_eq!(
        term("a ^ b ^ c"),
        "(INFIX_TERM (REF a) ^ (INFIX_TERM (REF b) ^ (REF c)))"
    );
}

#[test]
fn arrows_are_right_associative_and_loosest() {
    assert_eq!(
        term("a → b → c"),
        "(ARROW_TERM (REF a) → (ARROW_TERM (REF b) → (REF c)))"
    );
    // Relations bind tighter than `→`, so this is an implication between two
    // equations rather than an equation between an `a` and an arrow.
    assert_eq!(
        term("a = b → c = d"),
        "(ARROW_TERM (INFIX_TERM (REF a) = (REF b)) → (INFIX_TERM (REF c) = (REF d)))"
    );
}

#[test]
fn negation_binds_looser_than_equality() {
    assert_eq!(
        term("¬ a = b"),
        "(PREFIX_TERM ¬ (INFIX_TERM (REF a) = (REF b)))"
    );
}

#[test]
fn application_binds_tightest_and_is_flat() {
    assert_eq!(term("f a b"), "(APP (REF f) (REF a) (REF b))");
    assert_eq!(
        term("f a + g b"),
        "(INFIX_TERM (APP (REF f) (REF a)) + (APP (REF g) (REF b)))"
    );
}

#[test]
fn big_terms_are_not_bare_arguments_but_a_trailing_lambda_is() {
    // `do` is not an argument, which is what makes `for x in xs do …` work.
    assert_eq!(
        shape("def f := do\n  for i in [0:10] do\n    g i\n"),
        "(SOURCE_FILE (DEF (DECL_MODIFIERS) def (DECL_ID f) (DECL_SIG (BINDERS)) \
         (DECL_BODY := (DO_TERM do (DO_SEQ (DO_FOR for (BINDERS (REF i) in \
         (RANGE_LIT [ (LITERAL 0) : (LITERAL 10) ])) do (DO_SEQ (DO_EXPR \
         (APP (REF g) (REF i))))))))))"
    );
    // A trailing lambda, however, is an argument: `xs.map fun x => x + 1`.
    assert_eq!(
        term("xs.map fun x => x"),
        "(APP (REF xs.map) (FUN fun (BINDERS (SIMPLE_BINDER x)) => (REF x)))"
    );
}

#[test]
fn field_access_requires_adjacency() {
    // `(g x).field` is a projection...
    assert_eq!(
        term("(g x).field"),
        "(FIELD_ACCESS (PAREN_TERM ( (APP (REF g) (REF x)) )) . field)"
    );
    // ...but with a space, `.field` is an anonymous constructor argument.
    assert_eq!(term("g .field"), "(APP (REF g) (DOT_IDENT . field))");
}

#[test]
fn dependent_arrows_are_distinguished_from_ascriptions() {
    assert_eq!(
        term("(x : α) → β x"),
        "(DEP_ARROW (PAREN_BINDER ( x (TYPE_SPEC : (REF α)) )) → (APP (REF β) (REF x)))"
    );
    assert_eq!(term("(x : α)"), "(TYPE_ASCRIPTION ( (REF x) : (REF α) ))");
}

// ---- Layout ----------------------------------------------------------------

#[test]
fn a_nested_by_block_ends_at_the_dedent() {
    // The inner `by` must not swallow `exact h`, which belongs to the outer
    // block. This is the case indentation-insensitive parsing gets wrong.
    let src = "\
theorem t (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  have hp' : p := by
    exact hp
  exact ⟨hp', hq⟩
";
    let parse = lean4_syntax::parse(src);
    assert!(parse.ok(), "{:?}", parse.errors());
    let seqs: Vec<_> = parse
        .syntax()
        .descendants()
        .filter(|n| n.kind() == lean4_syntax::SyntaxKind::TACTIC_SEQ)
        .collect();
    // The outer block holds `have` and `exact`; the inner holds only `exact hp`.
    let outer = TacticSeq::cast(seqs[0].clone()).expect("a tactic sequence");
    let inner = TacticSeq::cast(seqs[1].clone()).expect("a nested tactic sequence");
    assert_eq!(
        outer.tactics().count(),
        2,
        "outer block should hold `have` and `exact`:\n{}",
        sexpr(&seqs[0])
    );
    assert_eq!(inner.tactics().count(), 1);
}

#[test]
fn an_application_never_absorbs_the_next_line() {
    // `bar` is dedented to column 0, so it starts a new command rather than
    // becoming an argument of `foo`.
    let parse = lean4_syntax::parse("#check foo\n#check bar\n");
    assert!(parse.ok(), "{:?}", parse.errors());
    let hashes = parse
        .syntax()
        .descendants()
        .filter(|n| n.kind() == lean4_syntax::SyntaxKind::HASH_CMD)
        .count();
    assert_eq!(hashes, 2);
}

#[test]
fn calc_steps_may_be_less_indented_than_the_first() {
    // The first step shares the `calc` line; later steps sit further left.
    let src = "\
theorem t (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c :=
  calc a = b := h1
    _ = c := h2
";
    let parse = lean4_syntax::parse(src);
    assert!(parse.ok(), "{:?}", parse.errors());
    let steps = parse
        .syntax()
        .descendants()
        .filter(|n| n.kind() == lean4_syntax::SyntaxKind::CALC_STEP)
        .count();
    assert_eq!(
        steps,
        2,
        "{}",
        lean4_syntax::syntax::debug_tree(&parse.syntax())
    );
}

#[test]
fn match_alternatives_may_start_at_column_zero() {
    let src = "\
def f (x : Nat) := match x with
| 0 => a
| _ => b
";
    let parse = lean4_syntax::parse(src);
    assert!(parse.ok(), "{:?}", parse.errors());
    let alts = parse
        .syntax()
        .descendants()
        .filter(|n| n.kind() == lean4_syntax::SyntaxKind::MATCH_ALT)
        .count();
    assert_eq!(alts, 2);
}

#[test]
fn nested_matches_are_separated_by_indentation() {
    let src = "\
def f (x y : Nat) := match x with
  | 0 => match y with
    | 0 => a
    | _ => b
  | _ => c
";
    let parse = lean4_syntax::parse(src);
    assert!(parse.ok(), "{:?}", parse.errors());
    let outer = parse
        .syntax()
        .descendants()
        .find(|n| n.kind() == lean4_syntax::SyntaxKind::MATCH_ALTS)
        .unwrap();
    assert_eq!(
        outer
            .children()
            .filter(|n| n.kind() == lean4_syntax::SyntaxKind::MATCH_ALT)
            .count(),
        2,
        "outer match should have exactly two alternatives:\n{}",
        sexpr(&outer)
    );
}

#[test]
fn tactic_alternatives_stay_inside_their_tactic() {
    let src = "\
theorem t (n : Nat) : True := by
  induction n with
  | zero => trivial
  | succ k ih => trivial
";
    let parse = lean4_syntax::parse(src);
    assert!(parse.ok(), "{:?}", parse.errors());
    let alts = parse
        .syntax()
        .descendants()
        .filter(|n| n.kind() == lean4_syntax::SyntaxKind::MATCH_ALT)
        .count();
    assert_eq!(
        alts,
        2,
        "{}",
        lean4_syntax::syntax::debug_tree(&parse.syntax())
    );
}

// ---- Error recovery --------------------------------------------------------

#[test]
fn a_broken_command_does_not_break_the_rest_of_the_file() {
    let parse = lean4_syntax::parse("def good1 := 1\ndef := := :=\ndef good2 := 2\n");
    assert!(!parse.ok(), "expected an error to be reported");

    let file = SourceFile::cast(parse.syntax()).unwrap();
    let names: Vec<String> = file
        .declarations()
        .filter_map(|d| d.name().map(|n| n.text().to_string()))
        .collect();
    assert_eq!(names, ["good1", "good2"]);

    // The broken region is preserved as an ERROR node, not discarded.
    let errors = parse
        .syntax()
        .descendants()
        .filter(|n| n.kind() == lean4_syntax::SyntaxKind::ERROR)
        .count();
    assert_eq!(errors, 1);
}

#[test]
fn errors_carry_source_ranges() {
    let src = "def f := 1\n)))\n";
    let parse = lean4_syntax::parse(src);
    assert!(!parse.ok());
    let err = &parse.errors()[0];
    let start = u32::from(err.range.start()) as usize;
    assert!(
        src[start..].starts_with(')'),
        "error range should point at the stray paren, got {:?}",
        &src[start..]
    );
}

/// A tactic inside a comma-separated list ends at the comma, so an anonymous
/// constructor of `by` blocks keeps one child per proof (#18).
#[test]
fn a_comma_ends_a_tactic_only_where_a_comma_separates_items() {
    use lean4_syntax::SyntaxKind;

    let parse = lean4_syntax::parse("theorem a : P ∧ Q := ⟨by simp, by ring⟩\n");
    assert!(parse.ok(), "{:?}", parse.errors());
    let ctor = parse
        .syntax()
        .descendants()
        .find(|n| n.kind() == SyntaxKind::ANON_CTOR)
        .expect("anonymous constructor");
    assert_eq!(
        ctor.children()
            .filter(|n| n.kind() == SyntaxKind::BY_TERM)
            .count(),
        2,
        "each `by` block is its own proof:\n{}",
        lean4_syntax::syntax::sexpr(&ctor)
    );

    // The converse: outside a comma-separated list a comma separates a single
    // tactic's arguments, which is what made an unconditional rule cost 2.6%.
    let parse = lean4_syntax::parse("theorem c : P := by\n  use 1, 2\n");
    assert!(parse.ok(), "{:?}", parse.errors());
    let uses = parse
        .syntax()
        .descendants()
        .find(|n| n.kind() == SyntaxKind::TACTIC_TERM_LIST)
        .expect("`use` tactic");
    assert_eq!(
        uses.descendants()
            .filter(|n| n.kind() == SyntaxKind::LITERAL)
            .count(),
        2,
        "`use 1, 2` passes both arguments to one tactic:\n{}",
        lean4_syntax::syntax::sexpr(&uses)
    );
}

/// Several pattern groups may share one body, without separate alternatives
/// merging into one.
#[test]
fn pattern_groups_share_a_body_without_merging_alternatives() {
    use lean4_syntax::SyntaxKind;

    let parse =
        lean4_syntax::parse("example := match x with\n  | 0 => a\n  | 1 => b\n  | _ => c\n");
    assert!(parse.ok(), "{:?}", parse.errors());
    let alts = parse
        .syntax()
        .descendants()
        .find(|n| n.kind() == SyntaxKind::MATCH_ALTS)
        .expect("alternatives");
    assert_eq!(
        alts.children()
            .filter(|n| n.kind() == SyntaxKind::MATCH_ALT)
            .count(),
        3,
        "three bodies means three alternatives"
    );

    let parse = lean4_syntax::parse(
        "example := match a, b with\n  | ⊤, ⊤ | ⊤, (c : α) => le_rfl\n  | _, _ => h\n",
    );
    assert!(parse.ok(), "{:?}", parse.errors());
    let alts = parse
        .syntax()
        .descendants()
        .find(|n| n.kind() == SyntaxKind::MATCH_ALTS)
        .expect("alternatives");
    let groups: Vec<usize> = alts
        .children()
        .filter(|n| n.kind() == SyntaxKind::MATCH_ALT)
        .map(|a| {
            a.children()
                .filter(|n| n.kind() == SyntaxKind::PATTERNS)
                .count()
        })
        .collect();
    assert_eq!(groups, vec![2, 1], "the first alternative has two groups");
}
