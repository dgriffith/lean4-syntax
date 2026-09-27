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

// ---- The parse tail (#17) --------------------------------------------------

#[test]
fn absolute_value_coexists_with_the_alternative_separator() {
    // `|` is also the match-alternative separator, the `rcases` alternation and
    // the `first | …` branch marker. It is safe here because those are matched
    // by explicit `tok(PIPE)` rules rather than through the term parser, and
    // because a wrong attempt dies at the missing closing `|`.
    assert_eq!(count("def d := |x|\n", NOTATION_BRACKET), 1);
    assert_eq!(count("def d := f |x| + g |y|\n", NOTATION_BRACKET), 2);

    // All the structural uses still work.
    parse_clean("def f : Nat → Nat\n  | 0 => 1\n  | k + 1 => k\n");
    parse_clean("def s : Set Nat := {y | y > 0}\n");
    parse_clean("example : True := by\n  rcases h with a | b\n  · trivial\n  · trivial\n");
    parse_clean("example : True := by\n  first\n    | exact h\n    | trivial\n");
    parse_clean("inductive T where\n  | leaf\n  | node (l : T)\n");
}

#[test]
fn set_difference_and_factorial_are_operators() {
    assert_eq!(count("def d := s \\ t\n", INFIX_TERM), 1);
    // Factorial applies after a bracket and across whitespace; a `!` directly
    // after an identifier is part of that identifier.
    assert_eq!(count("def d := (n - 1)!\n", POSTFIX_TERM), 1);
    assert_eq!(count("def d := n !\n", POSTFIX_TERM), 1);
    // And `!b` is still boolean negation.
    assert_eq!(count("def d := !b\n", PREFIX_TERM), 1);
}

#[test]
fn a_coercion_may_be_an_application_argument() {
    // The operator table handles `↑` at the head of a term; arguments come from
    // the atom set, so it has to be an atom as well.
    let src = "def d := P n ↑m ↑n\n";
    assert_eq!(count(src, PREFIX_TERM), 2);
    parse_clean("def d := ↑↑m\n");
}

#[test]
fn a_number_after_a_projection_dot_is_an_index() {
    // `x.2.2` reaches a nested field; lexing `2.2` as a float broke it.
    let src = "def d := (f x).2.2\n";
    assert_eq!(count(src, PROJ), 2);
    // Floats are unaffected.
    assert_eq!(count("def d := 1.5\n", LITERAL), 1);
}

#[test]
fn indexing_is_told_from_a_list_argument_by_adjacency() {
    assert_eq!(count("def d := xs[n]\n", INDEX), 1);
    assert_eq!(count("def d := xs[n]?\n", INDEX), 1);
    assert_eq!(count("def d := xs[n]!\n", INDEX), 1);
    // With a space it is an argument, as in Lean.
    assert_eq!(count("def d := f [a, b]\n", INDEX), 0);
    assert_eq!(count("def d := f [a, b]\n", LIST_LIT), 1);
}

#[test]
fn hash_commands_take_a_docstring_and_an_in_clause() {
    // `#guard_msgs` checks output against the docstring above it.
    let src = "/-- info: 12 -/\n#guard_msgs in\n#norm_num (12 : Nat)\n";
    let parse = parse_clean(src);
    assert_eq!(count(src, HASH_CMD), 2, "{}", sexpr(&parse.syntax()));
}

#[test]
fn an_attribute_body_may_continue_at_column_zero() {
    // Inside brackets Lean imposes no column constraint, but the run that reads
    // an attribute's body was applying one.
    parse_clean("/-- doc -/\n@[to_additive\n/-- additive doc -/]\nlemma t (h : p) : p := h\n");
}

#[test]
fn extends_may_follow_the_result_type() {
    // mathlib writes both orders.
    parse_clean("structure S (R : Type u) : Type u\n    extends Add R where\n  mem : Nat\n");
    parse_clean("structure S extends T : Type where\n  mem : Nat\n");
}

#[test]
fn a_notation_may_be_scoped_to_another_namespace() {
    parse_clean("@[inherit_doc] scoped[Veroff] infixl:70 \" ⊚ \" => Veroff.f\n");
    parse_clean("/-- doc -/\nscoped[Veroff] notation \"x\" => y\n");
    parse_clean("local infixl:65 \" ⊕ \" => Sum\n");
}

#[test]
fn postfix_notation_binds_tighter_than_application() {
    // In `g ℕ ℤˣ ℤ` the `ˣ` belongs to `ℤ`, not to the whole application, so it
    // has to be a trailer rather than only an operator-table entry.
    let src = "def d := g n zˣ m\n";
    let parse = parse_clean(src);
    let app = parse
        .syntax()
        .descendants()
        .find(|n| n.kind() == APP)
        .expect("an application");
    assert_eq!(
        app.children().filter(|n| n.kind() == POSTFIX_TERM).count(),
        1,
        "the postfix applies to one argument:\n{}",
        sexpr(&app)
    );
    // Applied to a complete term it still works.
    assert_eq!(count("def d := (a + b)ᶜ\n", POSTFIX_TERM), 1);
    assert_eq!(count("def d := ‖x‖₊\n", POSTFIX_TERM), 1);
}

#[test]
fn isomorphism_composition_is_its_own_operator() {
    // `≪≫` is one token; lexing it as `≪` then `≫` left two operators adjacent.
    assert_eq!(count("def d := e ≪≫ f\n", INFIX_TERM), 1);
    assert_eq!(count("def d := m ≪ n\n", INFIX_TERM), 1);
}

#[test]
fn a_bound_variable_may_carry_several_restrictions() {
    // `∑ p ∈ s with pred, f p` — mathlib's filtered sum.
    parse_clean("def d := ∑ p ∈ G with Easy p, f p\n");
    parse_clean("def d := ∑ p ∈ G, f p\n");
    parse_clean("def d := ∃ x > 0, p x\n");
}

#[test]
fn a_bracketed_tactic_list_applies_one_per_goal() {
    let src = "example : True := by\n  constructor <;> [skip; trivial]\n";
    assert_eq!(count(src, TACTIC_SEQ_BRACKETED), 1);
    // The same tactic to all goals still parses.
    parse_clean("example : True := by\n  constructor <;> trivial\n");
}

#[test]
fn an_interpolated_string_may_embed_a_string() {
    // The embedded term is part of the literal, so a string inside it must not
    // terminate the outer one.
    parse_clean("def d := s!\"one of {\", \".intercalate names}\"\n");
    parse_clean("def d := m!\"{e} : {t}\"\n");
    // A brace in an ordinary string is just a brace.
    parse_clean("def d := \"{\"\n");
}

#[test]
fn constructor_docstrings_come_before_the_pipe() {
    // Not after it, which is where this parser looked.
    let src = "inductive R : Nat → Prop\n  /-- The base case. -/\n  | base : R 1\n  /-- The step. -/\n  | step {n} (h : R n) : R (n + 1)\n";
    let parse = parse_clean(src);
    assert_eq!(count(src, CTOR), 2, "{}", sexpr(&parse.syntax()));
}

#[test]
fn a_universe_level_may_be_an_expression() {
    // `AlgCat.{max u w}` — levels are terms, not only names.
    parse_clean("def d : M.{w} R ⥤ A.{max u w} R where\n  obj := f\n");
    assert_eq!(count("def d := Foo.{u, v}\n", UNIV_ARGS), 1);
}

#[test]
fn a_binder_restriction_may_be_notation() {
    // `∀ᵐ x ∂μ, p x` — the measure-theoretic binders.
    parse_clean("def d := ∀ᵐ x ∂volume.restrict (Icc 0 1), p x\n");
}

#[test]
fn an_ascription_may_omit_its_type() {
    // `(e :)` ascribes with the expected type.
    assert_eq!(count("def d := (f x (_ : M) :)\n", TYPE_ASCRIPTION), 2);
    assert_eq!(count("def d := (x : Nat)\n", TYPE_ASCRIPTION), 1);
}

#[test]
fn vector_notation_and_indexed_proofs() {
    assert_eq!(
        count("def d := AffineIndependent R ![A, B, C]\n", ARRAY_LIT),
        1
    );
    // `xs[i]'h` supplies the in-bounds proof.
    assert_eq!(count("def d := (p.cells[1]'p.one_lt).1\n", INDEX), 1);
}

#[test]
fn a_structure_instance_may_have_several_sources() {
    assert_eq!(
        count(
            "def d := { (f : A), (g f : B) with c := h f }\n",
            STRUCT_INST
        ),
        1
    );
    assert_eq!(count("def d := { s with x := 1 }\n", STRUCT_INST), 1);
}

#[test]
fn a_have_may_introduce_binders_without_a_name() {
    parse_clean("def d := fun k ↦ have {p} (pp : p.Prime) : p = 2 := by simp\n  trivial\n");
    // And the named form still works.
    parse_clean("def d := have h : p := hp\n  h\n");
}

#[test]
fn a_lambda_may_destructure_a_pair() {
    // `fun (a, b) => …`. A parenthesised binder is tried first, so `(x : T)` is
    // unaffected — it only falls through here at the comma.
    parse_clean("def d := xs.map fun (a, b) => a + b\n");
    parse_clean("def d := xs.map fun ⟨a, b⟩ => a + b\n");
    parse_clean("def f (x : Nat) (y : Nat) : Nat := x + y\n");
    parse_clean("variable (α β : Type) [Inhabited α]\n");
}
