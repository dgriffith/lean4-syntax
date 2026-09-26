//! Tests for the typed views over the tree.

use lean4_syntax::ast::{AstNode, Binder, Command, Decl, HasDecl, Ref, SourceFile, Term};

fn file(src: &str) -> SourceFile {
    let parse = lean4_syntax::parse(src);
    assert!(parse.ok(), "unexpected errors: {:?}", parse.errors());
    SourceFile::cast(parse.syntax()).expect("root is a source file")
}

#[test]
fn a_definition_exposes_its_parts() {
    let f = file(
        "/-- Doubles a number. -/\n@[simp, inline]\nprivate def double (n : Nat) : Nat := n + n\n",
    );
    let Some(Command::Def(def)) = f.commands().next() else {
        panic!("expected a def")
    };

    assert_eq!(def.name().unwrap().text(), "double");
    assert_eq!(
        def.doc_comment().unwrap().text(),
        "/-- Doubles a number. -/"
    );
    assert!(def.modifiers().unwrap().is_private());

    let attrs: Vec<String> = def.attributes().iter().map(|a| a.text()).collect();
    assert_eq!(attrs, ["simp", "inline"]);

    let binders: Vec<String> = def
        .binders()
        .unwrap()
        .iter()
        .flat_map(|b| b.names().map(|n| n.text().to_string()).collect::<Vec<_>>())
        .collect();
    assert_eq!(binders, ["n"]);

    assert_eq!(def.ty().unwrap().text(), "Nat");
    assert!(matches!(def.value(), Some(Term::Infix(_))));
}

#[test]
fn implicit_and_instance_binders_are_distinguishable() {
    let f = file("def f {α : Type} [Monad m] ⦃β : Type⦄ (x : α) : α := x\n");
    let Some(Command::Def(def)) = f.commands().next() else {
        panic!()
    };
    let binders: Vec<(String, bool)> = def
        .binders()
        .unwrap()
        .iter()
        .map(|b| {
            let name = b
                .names()
                .map(|n| n.text().to_string())
                .collect::<Vec<_>>()
                .join(",");
            (name, b.is_implicit())
        })
        .collect();
    assert_eq!(
        binders,
        [
            ("α".to_string(), true),
            // An anonymous instance binder introduces no name of its own —
            // Lean synthesises one — so `names()` is empty here.
            (String::new(), true),
            ("β".to_string(), true),
            ("x".to_string(), false),
        ]
    );

    let inst = def.binders().unwrap().iter().nth(1).unwrap();
    assert!(matches!(inst, Binder::Inst(_)));
    assert_eq!(inst.ty().unwrap().text(), "Monad m");

    // A named instance binder does expose its name.
    let g = file("def g [inst : Monad m] : Nat := 1\n");
    let Some(Command::Def(gdef)) = g.commands().next() else {
        panic!()
    };
    let named = gdef.binders().unwrap().iter().next().unwrap();
    assert_eq!(
        named
            .names()
            .map(|n| n.text().to_string())
            .collect::<Vec<_>>(),
        ["inst"]
    );
}

#[test]
fn inductive_constructors_are_reachable() {
    let f = file(
        "inductive Tree (α : Type) where\n  | leaf\n  | node (l : Tree α) (v : α) (r : Tree α)\n",
    );
    let Some(Command::Inductive(ind)) = f.commands().next() else {
        panic!()
    };
    assert_eq!(ind.name().unwrap().text(), "Tree");
    let ctors: Vec<String> = ind
        .ctors()
        .map(|c| c.name().unwrap().text().to_string())
        .collect();
    assert_eq!(ctors, ["leaf", "node"]);

    let node_args: Vec<String> = ind
        .ctors()
        .nth(1)
        .unwrap()
        .binders()
        .unwrap()
        .iter()
        .flat_map(|b| b.names().map(|n| n.text().to_string()).collect::<Vec<_>>())
        .collect();
    assert_eq!(node_args, ["l", "v", "r"]);
}

#[test]
fn structure_fields_carry_names_types_and_docs() {
    let f = file("structure Point where\n  /-- horizontal -/\n  x : Float := 0.0\n  y : Float\n");
    let Some(Command::Structure(s)) = f.commands().next() else {
        panic!()
    };
    let fields: Vec<(String, String)> = s
        .fields()
        .map(|fl| {
            (
                fl.name().unwrap().text().to_string(),
                fl.ty().unwrap().text(),
            )
        })
        .collect();
    assert_eq!(
        fields,
        [
            ("x".to_string(), "Float".to_string()),
            ("y".to_string(), "Float".to_string())
        ]
    );
    assert_eq!(
        s.fields().next().unwrap().doc_comment().unwrap().text(),
        "/-- horizontal -/"
    );
}

#[test]
fn declarations_nested_in_namespaces_are_found() {
    let f =
        file("namespace A\ndef x := 1\nnamespace B\ntheorem y : True := trivial\nend B\nend A\n");
    let names: Vec<String> = f
        .declarations()
        .filter_map(|d| d.name().map(|n| n.text().to_string()))
        .collect();
    assert_eq!(names, ["x", "y"]);
}

#[test]
fn application_splits_into_function_and_arguments() {
    let f = file("def r := Nat.add x (y + 1) z\n");
    let Some(Command::Def(def)) = f.commands().next() else {
        panic!()
    };
    let Some(Term::App(app)) = def.value() else {
        panic!("expected an application")
    };
    assert_eq!(app.function().unwrap().text(), "Nat.add");
    let args: Vec<String> = app.args().map(|a| a.text()).collect();
    assert_eq!(args, ["x", "(y + 1)", "z"]);
}

#[test]
fn match_alternatives_expose_patterns_and_bodies() {
    let f = file("def f (x : Nat) := match x with\n  | 0 => a\n  | n + 1 => b\n");
    let Some(Command::Def(def)) = f.commands().next() else {
        panic!()
    };
    let Some(Term::Match(m)) = def.value() else {
        panic!("expected a match")
    };
    let discrs: Vec<String> = m.discriminants().map(|d| d.text()).collect();
    assert_eq!(discrs, ["x"]);

    let alts: Vec<(String, String)> = m
        .alts()
        .map(|alt| {
            let pats = alt
                .patterns()
                .map(|p| p.text())
                .collect::<Vec<_>>()
                .join(", ");
            (pats, alt.body().unwrap().text())
        })
        .collect();
    assert_eq!(
        alts,
        [
            ("0".to_string(), "a".to_string()),
            ("n + 1".to_string(), "b".to_string())
        ]
    );
}

#[test]
fn tactics_are_named_and_their_arguments_retained() {
    let f = file("theorem t : True := by\n  simp [Nat.add_comm, foo]\n  trivial\n");
    let Some(Command::Theorem(thm)) = f.commands().next() else {
        panic!()
    };
    let Some(Term::By(by)) = thm.value() else {
        panic!("expected a by block")
    };
    let names: Vec<String> = by
        .tactics()
        .unwrap()
        .tactics()
        .filter_map(lean4_syntax::ast::Tactic::cast)
        .map(|t| t.name().unwrap().text().to_string())
        .collect();
    assert_eq!(names, ["simp", "trivial"]);

    let first = by
        .tactics()
        .unwrap()
        .tactics()
        .next()
        .and_then(lean4_syntax::ast::Tactic::cast)
        .unwrap();
    assert_eq!(first.args().unwrap().text(), "[Nat.add_comm, foo]");
}

#[test]
fn every_reference_in_a_file_can_be_walked() {
    let parse = lean4_syntax::parse("def f (n : Nat) : Nat := Nat.succ (g n)\n");
    let refs: Vec<String> = parse
        .syntax()
        .descendants()
        .filter_map(Ref::cast)
        .map(|r| r.name().unwrap().text().to_string())
        .collect();
    assert_eq!(refs, ["Nat", "Nat", "Nat.succ", "g", "n"]);
}

#[test]
fn casting_rejects_mismatched_kinds() {
    let parse = lean4_syntax::parse("def f := 1");
    let root = parse.syntax();
    assert!(SourceFile::cast(root.clone()).is_some());
    assert!(Decl::cast(root.clone()).is_none());
    assert!(Term::cast(root).is_none());
}
