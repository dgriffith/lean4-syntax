//! Tests for the HIR and its lowering.
//!
//! Three properties matter more than any individual shape:
//!
//! * Lowering is **total** — it never panics and never drops syntax.
//! * `Opaque` is the **only** escape hatch, which is what makes coverage
//!   measurable.
//! * Derived equality is **structural** — two identical subterms compare equal
//!   regardless of where they appear, which is what analysis depends on.

use lean4_syntax::hir::{
    self, ArmBody, Explicitness, ItemKind, Lit, Module, Name, Precedence, QuantifierKind, Term,
};

fn lower(src: &str) -> Module {
    let parse = lean4_syntax::parse(src);
    hir::lower(&parse.syntax())
}

/// Lowers a definition and returns its value term.
fn value(src: &str) -> (Module, Term) {
    let module = lower(&format!("def f := {src}\n"));
    let (_, item) = module.items().next().expect("one item");
    let id = item.value.expect("a value");
    let term = module[id].clone();
    (module, term)
}

// ---- Totality --------------------------------------------------------------

#[test]
fn lowering_is_total_on_malformed_input() {
    // Anything that parses must lower, including what does not parse cleanly.
    for src in [
        "",
        "def",
        "def f :=",
        "def f := )",
        "def f := ((((",
        ":= := :=",
        "/- unterminated",
        "theorem t : p := by\n",
        "def f := 1\n@#$%^\ndef g := 2",
        "\u{1f600}",
    ] {
        let module = lower(src);
        // No assertion about *what* it produced — only that it did, without
        // panicking. The absence of a panic is the test.
        let _ = module.items().count();
    }
}

#[test]
fn every_corpus_file_lowers_without_errors_or_panics() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data");
    let mut checked = 0;
    for entry in std::fs::read_dir(&dir).expect("corpus directory") {
        let path = entry.expect("entry").path();
        if path.extension().is_none_or(|e| e != "lean") {
            continue;
        }
        let src = std::fs::read_to_string(&path).expect("readable");
        let module = lower(&src);
        assert!(
            module.errors.is_empty(),
            "{} produced lowering errors: {:#?}",
            path.display(),
            module.errors
        );
        checked += 1;
    }
    assert!(checked > 0);
}

#[test]
fn opaque_is_the_only_escape_hatch() {
    // An unmodelled tactic becomes opaque rather than an error, since it is a
    // deliberate boundary rather than a gap.
    let module = lower("theorem t : True := by\n  my_custom_tactic foo\n");
    assert!(module.errors.is_empty());
    assert_eq!(module.opaque_count(), 1);
}

// ---- Structural equality ---------------------------------------------------

#[test]
fn derived_equality_is_shallow_and_same_term_is_structural() {
    // The distinction that matters, and the one that is easy to get backwards.
    // `==` compares children by *id*, which is an arena position, so two
    // identical subterms in different places are not `==`. `same_term` compares
    // structure. An analysis using the wrong one would silently miss every
    // repeated subterm.
    let module = lower("def f := (a + b, a + b)\n");
    let sums: Vec<(hir::TermId, &Term)> = module
        .terms()
        .filter(|(_, t)| matches!(t, Term::Infix { .. }))
        .collect();
    assert_eq!(sums.len(), 2, "two `a + b` terms");

    assert_ne!(
        sums[0].1, sums[1].1,
        "`==` sees different child ids, since ids are arena positions"
    );
    assert!(
        module.same_term(sums[0].0, sums[1].0),
        "but the two terms have the same structure"
    );
}

#[test]
fn structural_comparison_sees_through_binders_and_tactics() {
    // Binders, patterns and tactics are reached by id too, so comparison has to
    // resolve them rather than compare the ids.
    let module = lower("def f := (fun x => x + 1, fun x => x + 1)\n");
    let funs: Vec<(hir::TermId, &Term)> = module
        .terms()
        .filter(|(_, t)| matches!(t, Term::Fun { .. }))
        .collect();
    assert_eq!(funs.len(), 2);
    assert!(module.same_term(funs[0].0, funs[1].0));

    // Tactic bodies compare structurally too.
    let module = lower("theorem t : True := by\n  refine ⟨?_, ?_⟩\n  · simp\n  · simp\n");
    let focuses: Vec<(hir::TacticId, &hir::Tactic)> = module
        .tactics()
        .filter(|(_, t)| matches!(t, hir::Tactic::Focus(_)))
        .collect();
    assert_eq!(focuses.len(), 2);
    assert!(module.same_tactic(focuses[0].0, focuses[1].0));
}

#[test]
fn structural_comparison_distinguishes_different_terms() {
    // The property that makes it useful: it must also say no.
    let module = lower("def f := (a + b, a + c)\n");
    let sums: Vec<(hir::TermId, &Term)> = module
        .terms()
        .filter(|(_, t)| matches!(t, Term::Infix { .. }))
        .collect();
    assert!(!module.same_term(sums[0].0, sums[1].0));

    // Operators of the same shape but different precedence provenance differ.
    let module = lower("def f := (a ≫ b, a ⊸ b)\n");
    let ops: Vec<(hir::TermId, &Term)> = module
        .terms()
        .filter(|(_, t)| matches!(t, Term::Infix { .. }))
        .collect();
    assert!(!module.same_term(ops[0].0, ops[1].0));
}

#[test]
fn a_visitor_reaches_every_child_of_a_node() {
    // One visitor backs traversal, comparison and id remapping; if it missed a
    // field, all three would be quietly wrong.
    let module = lower("def f := g x (p := e) + h\n");
    let (root, _) = module
        .terms()
        .find(|(_, t)| matches!(t, Term::Infix { .. }))
        .expect("an infix term");
    let refs = module.term_refs(root);
    assert_eq!(refs.terms.len(), 2, "an infix term has two operands");

    let (app, _) = module
        .terms()
        .find(|(_, t)| matches!(t, Term::App { .. }))
        .expect("an application");
    let refs = module.term_refs(app);
    assert_eq!(
        refs.terms.len(),
        3,
        "a function and two arguments, the named one included"
    );
}

#[test]
fn opaque_equality_is_positional_and_that_is_deliberate() {
    // Two uninterpreted regions are not known to be equal, so they are not.
    let module = lower("theorem t : True := by\n  custom_tac\n  custom_tac\n");
    let opaques: Vec<_> = module
        .tactics()
        .map(|(_, t)| t)
        .filter(|t| matches!(t, hir::Tactic::Opaque { .. }))
        .collect();
    assert_eq!(opaques.len(), 2);
    assert_ne!(
        opaques[0], opaques[1],
        "uninterpreted regions must not be assumed equal"
    );
}

// ---- The source map --------------------------------------------------------

#[test]
fn every_node_links_back_to_its_syntax() {
    let src = "def double (n : Nat) : Nat := n + n\n";
    let parse = lean4_syntax::parse(src);
    let root = parse.syntax();
    let module = hir::lower(&root);

    for (id, _) in module.terms() {
        let ptr = module
            .source
            .node(hir::HirId::Term(id))
            .expect("a source link");
        // And the pointer resolves against the tree it came from.
        assert!(ptr.try_to_node(&root).is_some());
    }
}

#[test]
fn a_source_position_maps_back_to_a_hir_node() {
    // This direction is what Lean's InfoTree needs: it reports goal states by
    // source position, and they have to attach to something.
    let src = "def f := a + b\n";
    let parse = lean4_syntax::parse(src);
    let root = parse.syntax();
    let module = hir::lower(&root);

    let infix_cst = root
        .descendants()
        .find(|n| n.kind() == lean4_syntax::SyntaxKind::INFIX_TERM)
        .expect("an infix node");
    let ptr = rowan::ast::SyntaxNodePtr::new(&infix_cst);
    let hir_id = module.source.hir(ptr).expect("a reverse link");
    let hir::HirId::Term(term_id) = hir_id else {
        panic!("expected a term")
    };
    assert!(matches!(module[term_id], Term::Infix { .. }));
}

// ---- Shapes ----------------------------------------------------------------

#[test]
fn an_assumed_precedence_survives_lowering() {
    // The parser records whether an operator's precedence was guessed; that has
    // to reach anything reasoning about associativity.
    let (_, term) = value("a ⊸ b");
    let Term::Infix { op, precedence, .. } = term else {
        panic!("expected an infix term, got {term:?}")
    };
    assert_eq!(op, Name::from("⊸"));
    assert_eq!(precedence, Precedence::Assumed);

    let (_, curated) = value("f ≫ g");
    let Term::Infix { precedence, .. } = curated else {
        panic!()
    };
    assert_eq!(precedence, Precedence::Known);
}

#[test]
fn parentheses_are_dropped_but_ascriptions_are_not() {
    let (_, term) = value("(a + b)");
    assert!(
        matches!(term, Term::Infix { .. }),
        "grouping carries no meaning of its own, got {term:?}"
    );
    let (_, ascribed) = value("(a : Nat)");
    assert!(matches!(ascribed, Term::Ascription { .. }));
}

#[test]
fn applications_keep_named_arguments() {
    let (module, term) = value("g x (p := e)");
    let Term::App { args, .. } = term else {
        panic!("expected an application, got {term:?}")
    };
    assert_eq!(args.len(), 2);
    assert_eq!(args[0].name, None);
    assert_eq!(args[1].name, Some(Name::from("p")));
    assert!(matches!(module[args[1].value], Term::Ref(_)));
}

#[test]
fn literals_keep_their_spelling() {
    // `0x10` and `16` mean the same thing but must not be interchanged in
    // someone's source.
    let (_, term) = value("0x10");
    assert_eq!(term, Term::Lit(Lit::Nat("0x10".into())));
    let (_, s) = value("\"hi\"");
    assert_eq!(s, Term::Lit(Lit::Str("\"hi\"".into())));
}

#[test]
fn quantifiers_and_big_operators_share_a_shape() {
    let (module, term) = value("∀ x : Nat, p x");
    let Term::Quantifier { kind, binders, .. } = term else {
        panic!("expected a quantifier, got {term:?}")
    };
    assert_eq!(kind, QuantifierKind::Forall);
    assert_eq!(module[binders[0]].names, vec![Name::from("x")]);

    let (_, sum) = value("∑ i, f i");
    let Term::Quantifier { kind, .. } = sum else {
        panic!()
    };
    assert_eq!(kind, QuantifierKind::BigOperator(Name::from("∑")));
}

#[test]
fn binder_explicitness_is_preserved() {
    let module = lower("def f {α : Type} [Monad m] ⦃β : Type⦄ (x : α) := x\n");
    let kinds: Vec<Explicitness> = module.binders().map(|(_, b)| b.explicitness).collect();
    assert_eq!(
        kinds,
        [
            Explicitness::Implicit,
            Explicitness::Instance,
            Explicitness::StrictImplicit,
            Explicitness::Explicit,
        ]
    );
}

#[test]
fn a_have_separates_its_value_from_its_body() {
    // The layout bug this exposed in the parser: the body must not be an
    // argument of the value.
    let module = lower("def f :=\n  have h : T := g x\n  h\n");
    let have = module
        .terms()
        .map(|(_, t)| t)
        .find(|t| matches!(t, Term::Have { .. }))
        .expect("a have term");
    let Term::Have {
        value, body, ty, ..
    } = have
    else {
        unreachable!()
    };
    assert!(ty.is_some());
    assert!(matches!(module[value.expect("a value")], Term::App { .. }));
    assert!(matches!(module[*body], Term::Ref(_)));
}

#[test]
fn match_alternatives_carry_patterns_and_bodies() {
    let module = lower("def f (x : Nat) := match x with\n  | 0 => a\n  | n + 1 => b\n");
    let arms = module
        .terms()
        .filter_map(|(_, t)| match t {
            Term::Match { arms, .. } => Some(arms.clone()),
            _ => None,
        })
        .next()
        .expect("a match");
    assert_eq!(arms.len(), 2);
    assert!(matches!(arms[0].body, ArmBody::Term(_)));
}

#[test]
fn tactic_alternatives_carry_tactic_bodies() {
    // The same `Arm` type, with a tactic right-hand side.
    let module = lower(
        "theorem t (n : Nat) : True := by\n  induction n with\n  | zero => trivial\n  | succ k ih => trivial\n",
    );
    let arms = module
        .tactics()
        .filter_map(|(_, t)| match t {
            hir::Tactic::Cases { arms, .. } if !arms.is_empty() => Some(arms.clone()),
            _ => None,
        })
        .next()
        .expect("an induction tactic");
    assert_eq!(arms.len(), 2);
    assert!(matches!(arms[0].body, ArmBody::Tactic(_)));
}

#[test]
fn simp_arguments_and_locations_survive_lowering() {
    let module = lower("theorem t : True := by\n  simp only [foo, ← bar, -baz, *] at h ⊢\n");
    let simp = module
        .tactics()
        .map(|(_, t)| t)
        .find(|t| matches!(t, hir::Tactic::Simp { .. }))
        .expect("a simp tactic");
    let hir::Tactic::Simp {
        only,
        args,
        location,
        ..
    } = simp
    else {
        unreachable!()
    };
    assert!(*only);
    assert_eq!(args.len(), 4);
    assert!(matches!(
        args[1],
        hir::SimpArg::Lemma { reversed: true, .. }
    ));
    assert!(matches!(args[2], hir::SimpArg::Removed(_)));
    assert_eq!(args[3], hir::SimpArg::Wildcard);
    let loc = location.as_ref().expect("a location");
    assert_eq!(loc.hypotheses, vec![Name::from("h")]);
    assert!(loc.goal);
}

#[test]
fn items_expose_names_docs_attributes_and_modifiers() {
    let module =
        lower("/-- Doubles. -/\n@[simp, inline]\nprivate def double (n : Nat) : Nat := n + n\n");
    let (_, item) = module.items().next().expect("an item");
    assert_eq!(item.kind, ItemKind::Def);
    assert_eq!(item.name, Some(Name::from("double")));
    assert_eq!(item.doc.as_deref(), Some("/-- Doubles. -/"));
    assert_eq!(item.attrs, ["simp", "inline"]);
    assert_eq!(item.modifiers, [Name::from("private")]);
    assert_eq!(item.binders.len(), 1);
    assert!(item.ty.is_some());
    assert!(item.value.is_some());
}

#[test]
fn inductives_and_structures_expose_their_parts() {
    let module = lower(
        "inductive Tree (α : Type) where\n  | leaf\n  | node (l : Tree α) (v : α)\n  deriving Repr, BEq\n",
    );
    let (_, item) = module.items().next().unwrap();
    assert_eq!(item.kind, ItemKind::Inductive);
    let names: Vec<&Name> = item.ctors.iter().map(|c| &c.name).collect();
    assert_eq!(names, [&Name::from("leaf"), &Name::from("node")]);
    assert_eq!(item.ctors[1].binders.len(), 2);
    assert_eq!(item.deriving, [Name::from("Repr"), Name::from("BEq")]);

    let module = lower("structure P where\n  /-- across -/\n  x : Float := 0.0\n  y : Float\n");
    let (_, item) = module.items().next().unwrap();
    assert_eq!(item.kind, ItemKind::Structure);
    assert_eq!(item.fields.len(), 2);
    assert_eq!(item.fields[0].name, Name::from("x"));
    assert!(item.fields[0].default.is_some());
    assert_eq!(item.fields[0].doc.as_deref(), Some("/-- across -/"));
}

#[test]
fn universe_arguments_are_a_term() {
    // `Foo.{u}` is a term-position node; missing it from the typed enum made
    // lowering report 618 spurious "missing operand" errors over mathlib.
    let (module, term) = value("AlgCat.{u} ≌ RingCat.{u}");
    let Term::Infix { rhs, .. } = term else {
        panic!("expected an infix term, got {term:?}")
    };
    let Term::Universes { levels, .. } = &module[rhs] else {
        panic!("expected universe arguments, got {:?}", module[rhs])
    };
    assert_eq!(levels.len(), 1);
    assert_eq!(module[levels[0]], Term::Ref(Name::from("u")));

    // A level may be an expression, not only a name.
    let (module, term) = value("AlgCat.{max u w} R");
    let univ = module
        .terms()
        .map(|(_, t)| t)
        .find(|t| matches!(t, Term::Universes { .. }))
        .expect("universe arguments");
    let Term::Universes { levels, .. } = univ else {
        unreachable!()
    };
    assert!(matches!(module[levels[0]], Term::App { .. }));
    let _ = term;
}

#[test]
fn a_do_block_lowers_to_statements() {
    let module = lower(
        "def m : IO Unit := do\n  let mut total := 0\n  for i in [0:10] do\n    total := total + i\n  IO.println total\n",
    );
    let stmts = module
        .terms()
        .filter_map(|(_, t)| match t {
            Term::Do(stmts) => Some(stmts.clone()),
            _ => None,
        })
        .next()
        .expect("a do block");
    assert_eq!(stmts.len(), 3);
    assert!(matches!(stmts[0], hir::DoStmt::Let { mutable: true, .. }));
    assert!(matches!(stmts[1], hir::DoStmt::For { .. }));
    assert!(matches!(stmts[2], hir::DoStmt::Expr(_)));
}

#[test]
fn a_name_splits_into_components() {
    let name = Name::from("Nat.succ.eq");
    assert_eq!(name.components().collect::<Vec<_>>(), ["Nat", "succ", "eq"]);
    assert_eq!(name.base(), "eq");
}

#[test]
fn deeply_nested_terms_do_not_abort_the_process() {
    // A machine-generated proof can nest far deeper than a human-written one,
    // and a stack overflow is an abort rather than a catchable panic — so it
    // would be worse than the panic totality is meant to rule out. Lowering and
    // structural comparison both grow the stack rather than trusting the
    // default, as the parser already does.
    let chain = std::iter::repeat_n("a", 3000)
        .collect::<Vec<_>>()
        .join(" + ");
    let src = format!("def f := ({chain}, {chain})\n");
    let module = lower(&src);
    let tuple = module
        .terms()
        .find_map(|(_, t)| match t {
            Term::Tuple(items) if items.len() == 2 => Some(items.clone()),
            _ => None,
        })
        .expect("a tuple of two chains");
    assert!(module.same_term(tuple[0], tuple[1]));
}

#[test]
fn nested_items_are_all_reachable() {
    // A `mutual` block holds several declarations. Capturing only the first
    // dropped the rest silently — nothing became `Opaque`, so no coverage
    // metric would have revealed the loss.
    let module = lower(
        "mutual\n  def isEven : Nat → Bool\n    | 0 => true\n  def isOdd : Nat → Bool\n    | 0 => false\nend\n",
    );
    let names: Vec<String> = module
        .items()
        .filter_map(|(_, i)| i.name.as_ref().map(|n| n.to_string()))
        .collect();
    assert_eq!(names, ["isEven", "isOdd"]);

    let (_, block) = module
        .items()
        .find(|(_, i)| matches!(i.kind, ItemKind::Other(_)))
        .expect("the mutual block");
    assert_eq!(block.nested.len(), 2, "both declarations are nested in it");

    // `variable (α) in <command>` nests exactly one.
    let module = lower("variable (α) in\nabbrev dim := 0\n");
    let (_, var) = module
        .items()
        .find(|(_, i)| i.kind == ItemKind::Variable)
        .expect("the variable command");
    assert_eq!(var.nested.len(), 1);
    assert_eq!(module[var.nested[0]].kind, ItemKind::Abbrev);
}
