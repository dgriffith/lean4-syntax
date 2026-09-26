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
