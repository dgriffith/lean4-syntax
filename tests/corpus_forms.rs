//! Forms found by running `examples/corpus_report.rs` over mathlib.
//!
//! Each of these was a parse failure discovered on real Lean rather than
//! imagined up front, and each is core-language syntax the hand-written corpus
//! simply never exercised. `tests/data/module_system.lean` keeps them parsing;
//! these tests pin what they parse *into*.

use lean4_syntax::SyntaxKind::*;
use lean4_syntax::ast::{AstNode, Command, HasDecl, SourceFile, Term};
use lean4_syntax::syntax::sexpr;

fn parse_clean(src: &str) -> lean4_syntax::Parse {
    let parse = lean4_syntax::parse(src);
    assert!(
        parse.ok(),
        "unexpected errors in {src:?}: {:?}",
        parse.errors()
    );
    parse
}

/// Counts nodes of a kind.
fn count(src: &str, kind: lean4_syntax::SyntaxKind) -> usize {
    parse_clean(src)
        .syntax()
        .descendants()
        .filter(|n| n.kind() == kind)
        .count()
}

#[test]
fn the_module_system_header_parses() {
    // Present in 8750 of mathlib's 9160 files, so this one gap accounted for
    // nearly every file failing.
    let src = "module\n\npublic import A.B\npublic meta import C.D\nmeta import E\nimport F\n";
    let parse = parse_clean(src);
    assert_eq!(count(src, MODULE_CMD), 1);
    let file = SourceFile::cast(parse.syntax()).unwrap();
    let imports = file
        .commands()
        .filter(|c| matches!(c, Command::Import(_)))
        .count();
    assert_eq!(imports, 4);
}

#[test]
fn sections_carry_attributes_and_modifiers() {
    // `@[expose] public section` and `noncomputable section` are both common.
    for src in [
        "section\n",
        "noncomputable section\n",
        "public section\n",
        "@[expose] public section\n",
        "@[expose] public noncomputable section\n",
        "public section Named\n",
    ] {
        assert_eq!(count(src, SECTION), 1, "failed on {src:?}");
    }
}

#[test]
fn declarations_take_module_visibility() {
    for src in [
        "public def f : Nat := 0\n",
        "meta def g : Nat := 0\n",
        "public theorem t : True := trivial\n",
    ] {
        parse_clean(src);
    }
}

#[test]
fn variable_in_scopes_binders_to_one_command() {
    let src = "variable (α) in\nabbrev dim := 0\n";
    let parse = parse_clean(src);
    // The inner command nests inside the `variable`, which is what makes the
    // scoping visible in the tree.
    let var = parse
        .syntax()
        .descendants()
        .find(|n| n.kind() == VARIABLE_CMD)
        .expect("a variable command");
    assert_eq!(
        var.descendants().filter(|n| n.kind() == ABBREV).count(),
        1,
        "{}",
        sexpr(&var)
    );
}

#[test]
fn structure_fields_take_modifiers_and_binders() {
    let src =
        "structure S (G : Type) where\n  protected toFun : G → G\n  bound (i : Nat) : i ≤ i\n";
    let parse = parse_clean(src);
    let Some(Command::Structure(st)) = SourceFile::cast(parse.syntax()).unwrap().commands().next()
    else {
        panic!("expected a structure")
    };
    let names: Vec<String> = st
        .fields()
        .map(|f| f.name().unwrap().text().to_string())
        .collect();
    assert_eq!(names, ["toFun", "bound"]);
}

#[test]
fn structure_instance_fields_may_be_separated_by_newlines() {
    // Lean does not require commas here. Before the fix, the value of one field
    // absorbed the name of the next as an application argument.
    let src = "def s : S := {  ac := 0\n                rs := fun _ => 0 }\n";
    let parse = parse_clean(src);
    assert_eq!(
        count(src, STRUCT_INST_FIELD),
        2,
        "{}",
        sexpr(&parse.syntax())
    );

    // The comma-separated form still works, as does a mix.
    assert_eq!(
        count("def s : S := { a := 1, b := 2 }\n", STRUCT_INST_FIELD),
        2
    );
}

#[test]
fn show_and_suffices_accept_a_tactic_proof() {
    // `show T by tac` is as common as `show T from e`.
    assert_eq!(count("def d := (show 1 < 3 by omega)\n", SHOW_TERM), 1);
    assert_eq!(count("def d := show 1 < 3 from h\n", SHOW_TERM), 1);
    assert_eq!(
        count(
            "theorem t (p : Prop) (hp : p) : p := by\n  suffices h : p by exact h\n  exact hp\n",
            TACTIC_HAVE
        ),
        1
    );
}

#[test]
fn array_literals_are_core_syntax() {
    assert_eq!(count("def a : Array Nat := #[1, 2, 3]\n", ARRAY_LIT), 1);
    assert_eq!(count("def a : Array Nat := #[]\n", ARRAY_LIT), 1);
    // `#check` is still a command, not an array.
    assert_eq!(count("#check foo\n", HASH_CMD), 1);
}

#[test]
fn coercion_arrows_are_prefix_operators() {
    let src = "def c (n : Nat) := ↑n + 1\n";
    let parse = parse_clean(src);
    // `↑` binds tighter than `+`, so the coercion applies to `n` alone.
    let Some(Command::Def(def)) = SourceFile::cast(parse.syntax()).unwrap().commands().next()
    else {
        panic!()
    };
    let Some(Term::Infix(add)) = def.value() else {
        panic!("expected `+` at the top, got {:?}", def.value())
    };
    assert_eq!(add.lhs().unwrap().text(), "↑n");
    for src in [
        "def c (f : Nat → Nat) := ⇑f\n",
        "def c (s : Set Nat) := ↥s\n",
    ] {
        parse_clean(src);
    }
}

#[test]
fn core_scoping_commands_are_recognised() {
    // These reached only the generic fallback before, with `nonrec` worse than
    // that: being read as a command detached it from the `def` it modifies.
    assert_eq!(count("export Nat (succ pred)\n", EXPORT_CMD), 1);
    assert_eq!(count("include h\n", INCLUDE_CMD), 1);
    assert_eq!(count("omit [Inhabited α] h\n", OMIT_CMD), 1);

    let src = "nonrec def f : Nat := 0\n";
    let parse = parse_clean(src);
    assert_eq!(
        count(src, UNKNOWN_CMD),
        0,
        "`nonrec` is a modifier, not a command"
    );
    let Some(Command::Def(def)) = SourceFile::cast(parse.syntax()).unwrap().commands().next()
    else {
        panic!("expected a def carrying the modifier")
    };
    assert!(
        def.modifiers()
            .unwrap()
            .keywords()
            .any(|k| k.text() == "nonrec")
    );
}

#[test]
fn unknown_commands_no_longer_cascade() {
    // mathlib defines many commands of its own. An unfamiliar one must not take
    // the declarations after it down with it.
    let src = "assert_not_exists Finset\nalias foo := Nat.succ\ndef after : Nat := 0\n";
    let parse = parse_clean(src);
    let file = SourceFile::cast(parse.syntax()).unwrap();
    assert_eq!(count(src, UNKNOWN_CMD), 2);
    let names: Vec<String> = file
        .declarations()
        .filter_map(|d| d.name().map(|n| n.text().to_string()))
        .collect();
    assert_eq!(names, ["after"], "the trailing def must still be reached");
}

#[test]
fn a_failed_declaration_is_contained_to_itself() {
    // Recovery resumes at the next column-0 token, so one bad declaration does
    // not swallow its neighbours.
    let src = "def a := 1\ndef b := ((((\ndef c := 3\n";
    let parse = lean4_syntax::parse(src);
    assert!(!parse.ok());
    let file = SourceFile::cast(parse.syntax()).unwrap();
    let names: Vec<String> = file
        .declarations()
        .filter_map(|d| d.name().map(|n| n.text().to_string()))
        .collect();
    assert!(
        names.contains(&"a".to_string()) && names.contains(&"c".to_string()),
        "expected a and c to survive, got {names:?}"
    );
}

// ---- Layout: constructs that parse in isolation but failed in place --------

#[test]
fn a_have_body_on_the_next_line_is_not_an_argument_of_its_value() {
    // Lean anchors `have` at its own keyword, so the value's arguments must be
    // indented past it and the body need only reach it. Anchoring at the
    // enclosing command instead made the body one more argument of `pair`.
    let src = "def n : Nat → Nat\n  | 0 => 0\n  | k =>\n    have ⟨t, ht⟩ := pair k\n    t\n";
    let parse = parse_clean(src);
    let have = parse
        .syntax()
        .descendants()
        .find(|n| n.kind() == HAVE_TERM)
        .expect("a have term");
    // Two direct term children: the value and the body, not one big application.
    let apps = have.children().filter(|n| n.kind() == APP).count();
    assert_eq!(
        apps,
        1,
        "the value should be the only application:\n{}",
        sexpr(&have)
    );
    assert!(
        have.children().any(|n| n.kind() == REF),
        "the body should be a reference of its own:\n{}",
        sexpr(&have)
    );
}

#[test]
fn let_show_and_suffices_anchor_the_same_way() {
    parse_clean("def n (k : Nat) : Nat :=\n  let ⟨a, b⟩ := pair k\n  a\n");
    parse_clean(
        "theorem t (p : Prop) (hp : p) : p := by\n  suffices h : p by exact h\n  exact hp\n",
    );
    parse_clean("theorem t (p : Prop) (hp : p) : p := by\n  show p\n  exact hp\n");
}

#[test]
fn a_midline_tactic_does_not_claim_the_next_line() {
    // `intros` sits mid-line, so the following line is dedented *relative to
    // it*. Its pattern list needs the same `colGt` guard application arguments
    // have, or `constructor` becomes one of its patterns.
    let src = "theorem t (a b : Nat) : a + b = b + a ∧ True := by\n  simp only [Nat.add_comm]; intros\n  constructor <;> (symm; assumption)\n";
    let parse = parse_clean(src);
    let intro = parse
        .syntax()
        .descendants()
        .find(|n| n.kind() == TACTIC_INTRO)
        .expect("an intros tactic");
    assert_eq!(
        intro
            .descendants()
            .filter(|n| n.kind() == RCASES_PAT)
            .count(),
        0,
        "`intros` takes no patterns here:\n{}",
        sexpr(&intro)
    );
    // And the bracketed block after `<;>` is reached.
    assert_eq!(count(src, TACTIC_SEQ_BRACKETED), 1);
}

#[test]
fn instance_introducing_let_and_have_need_no_name() {
    let src = "theorem t (p : Prop) : True := by\n  letI := Classical.propDecidable p\n  haveI := Classical.dec p\n  trivial\n";
    let parse = parse_clean(src);
    assert_eq!(count(src, TACTIC_HAVE), 2, "{}", sexpr(&parse.syntax()));
}

#[test]
fn an_unrecognised_command_may_carry_attributes() {
    // mathlib deprecates aliases this way, with the attribute on its own line.
    let src =
        "@[deprecated (since := \"2026-01-01\")]\nalias oldName := newName\n\ndef after := 0\n";
    let parse = parse_clean(src);
    assert_eq!(count(src, UNKNOWN_CMD), 1);
    let file = SourceFile::cast(parse.syntax()).unwrap();
    let names: Vec<String> = file
        .declarations()
        .filter_map(|d| d.name().map(|n| n.text().to_string()))
        .collect();
    assert_eq!(names, ["after"], "the following def must still be reached");
}

#[test]
fn spacing_separates_an_ellipsis_argument_from_a_range() {
    // `f (g ..)` leaves the rest to inference; `a..b` is a range.
    assert_eq!(count("def d := f (g ..)\n", HOLE), 1);
    let ranged = parse_clean("def d := ∫ x in a..b, f x\n");
    assert_eq!(
        ranged
            .syntax()
            .descendants()
            .filter(|n| n.kind() == HOLE)
            .count(),
        0,
        "`a..b` is a range, not an ellipsis"
    );
}

#[test]
fn an_import_list_stops_at_the_end_of_its_line() {
    // `import A.B` followed by an ident-led command was absorbing the command's
    // name as another module, because the module list was an unguarded
    // `repeated()`. Same class of bug as an application eating the next line.
    let src = "module\n\npublic import A.B\n\ndeprecated_module (since := \"2026-01-01\")\n";
    let parse = parse_clean(src);
    assert_eq!(count(src, IMPORT), 1);
    assert_eq!(count(src, UNKNOWN_CMD), 1);
    let import = parse
        .syntax()
        .descendants()
        .find(|n| n.kind() == IMPORT)
        .unwrap();
    assert_eq!(
        import
            .children_with_tokens()
            .filter_map(|it| it.into_token())
            .filter(|t| t.kind() == IDENT)
            .count(),
        1,
        "only `A.B` is a module name:\n{}",
        sexpr(&import)
    );
}

#[test]
fn instance_introducing_binders_work_in_term_position_too() {
    // `haveI` and `letI` are identifiers rather than keywords, so they need
    // their own path into the `have` shape.
    parse_clean(
        "def n : Nat :=\n  haveI : Inhabited Nat := inferInstanceAs (Inhabited Nat)\n  0\n",
    );
    parse_clean("def n : Nat :=\n  letI := Classical.propDecidable True\n  0\n");
}

#[test]
fn an_operator_may_stand_alone_in_parentheses() {
    // `((↑) : Rˣ → R)` passes the coercion itself as a function.
    parse_clean("def n := ((↑) : Nat → Int)\n");
    parse_clean("def n := (·) \n");
}

#[test]
fn field_abbreviation_does_not_swallow_set_literals() {
    // `{ cmd := c, args, env }` abbreviates two fields...
    assert_eq!(
        count("def n := { cmd := c, args, env }\n", STRUCT_INST_FIELD),
        3
    );
    // ...but `{a, b}` stays a set literal, since the forms are ambiguous in
    // surface syntax and Lean separates them by expected type.
    assert_eq!(count("def n : Set Nat := {a, b}\n", SET_LIT), 1);
    assert_eq!(count("def n : Set Nat := {a, b}\n", STRUCT_INST), 0);
}

#[test]
fn a_modifier_decorates_an_ascii_operator() {
    // `~ᵤ` is `Associated`, `=ᵐ` is almost-everywhere equality.
    parse_clean("def n (x z : Nat) := x ~ᵤ z\n");
    // Plain arithmetic is unaffected.
    assert_eq!(count("def n := a + b\n", INFIX_TERM), 1);
}
