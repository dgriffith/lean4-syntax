//! Coverage for the structured tactic grammar.
//!
//! Each test pins one tactic form, since the point of structuring tactics is
//! that a transformation can reach their parts by name rather than by
//! re-lexing an opaque token run.

use lean4_syntax::ast::{AstNode, Command, HasDecl, HasTacticName, SourceFile, Tactic, Term};
use lean4_syntax::syntax::sexpr;

/// Parses `by <tactics>` as a theorem body and returns the tactics.
fn tactics(body: &str) -> Vec<Tactic> {
    let src = format!("theorem t : True := by\n{body}\n");
    let parse = lean4_syntax::parse(&src);
    assert!(
        parse.ok(),
        "unexpected errors in {src:?}: {:?}",
        parse.errors()
    );
    let file = SourceFile::cast(parse.syntax()).unwrap();
    let Some(Command::Theorem(thm)) = file.commands().next() else {
        panic!("expected a theorem")
    };
    let Some(Term::By(by)) = thm.value() else {
        panic!("expected a by block, got:\n{}", sexpr(&parse.syntax()))
    };
    by.tactics()
        .expect("by block has tactics")
        .tactics()
        .collect()
}

/// Parses a single tactic.
fn one(body: &str) -> Tactic {
    let mut all = tactics(body);
    assert_eq!(all.len(), 1, "expected exactly one tactic from {body:?}");
    all.pop().unwrap()
}

// ---- simp-like -------------------------------------------------------------

#[test]
fn simp_arguments_are_classified() {
    let Tactic::Simp(simp) = one("  simp only [foo, ← bar, -baz, *] at h ⊢") else {
        panic!("expected simp")
    };
    assert_eq!(simp.name().unwrap().text(), "simp");
    assert!(simp.is_only());

    let args: Vec<_> = simp.args().collect();
    assert_eq!(args.len(), 4);
    assert_eq!(args[0].term().unwrap().text(), "foo");
    assert!(!args[0].is_reversed() && !args[0].is_removed() && !args[0].is_wildcard());
    assert!(args[1].is_reversed());
    assert_eq!(args[1].term().unwrap().text(), "bar");
    assert!(args[2].is_removed());
    assert_eq!(args[2].term().unwrap().text(), "baz");
    assert!(args[3].is_wildcard());
}

#[test]
fn simp_location_distinguishes_hypotheses_from_the_goal() {
    let Tactic::Simp(simp) = one("  simp at h1 h2 ⊢") else {
        panic!()
    };
    let loc = simp.location().unwrap();
    let hyps: Vec<String> = loc.hypotheses().map(|h| h.text().to_string()).collect();
    assert_eq!(hyps, ["h1", "h2"]);
    assert!(loc.includes_goal());
    assert!(!loc.is_everywhere());

    let Tactic::Simp(everywhere) = one("  simp at *") else {
        panic!()
    };
    assert!(everywhere.location().unwrap().is_everywhere());

    let Tactic::Simp(bare) = one("  simp") else {
        panic!()
    };
    assert!(bare.location().is_none());
    assert!(!bare.is_only());
}

#[test]
fn simp_config_is_kept_without_being_interpreted() {
    let Tactic::Simp(simp) = one("  simp (config := { decide := true }) [h]") else {
        panic!()
    };
    assert_eq!(
        simp.config().unwrap().text(),
        "(config := { decide := true })"
    );
    assert_eq!(simp.args().count(), 1);
}

#[test]
fn a_question_mark_suffix_does_not_hide_the_tactic_name() {
    // `?` is an identifier character in Lean, so `simp?` is a single token.
    let Tactic::Simp(simp) = one("  simp? [foo]") else {
        panic!("expected simp? to be recognised as simp-like")
    };
    assert_eq!(simp.name().unwrap().text(), "simp?");
    assert_eq!(simp.base_name().unwrap(), "simp");
}

#[test]
fn other_simp_like_tactics_share_the_shape() {
    for (body, name) in [
        ("  simp_all", "simp_all"),
        ("  norm_num [foo]", "norm_num"),
        ("  linarith [h1, h2]", "linarith"),
        ("  push_cast at h", "push_cast"),
        ("  omega", "omega"),
    ] {
        let Tactic::Simp(t) = one(body) else {
            panic!("{body} should be simp-like")
        };
        assert_eq!(t.name().unwrap().text(), name);
    }
}

// ---- rewrite-like ----------------------------------------------------------

#[test]
fn rewrite_rules_record_their_direction() {
    let Tactic::Rewrite(rw) = one("  rw [h1, ← h2] at h ⊢") else {
        panic!("expected rw")
    };
    let rules: Vec<_> = rw.rules().collect();
    assert_eq!(rules.len(), 2);
    assert!(!rules[0].is_reversed());
    assert_eq!(rules[0].term().unwrap().text(), "h1");
    assert!(rules[1].is_reversed());
    assert_eq!(rules[1].term().unwrap().text(), "h2");
    assert!(rw.location().unwrap().includes_goal());
}

#[test]
fn nth_rewrite_records_which_occurrence() {
    let Tactic::Rewrite(rw) = one("  nth_rw 2 [h]") else {
        panic!()
    };
    assert_eq!(rw.occurrence().unwrap().text(), "2");
    assert_eq!(rw.rules().count(), 1);
}

// ---- term-taking -----------------------------------------------------------

#[test]
fn term_tactics_expose_their_term() {
    for (body, name, term) in [
        ("  exact h.symm", "exact", "h.symm"),
        ("  apply Nat.le_of_lt", "apply", "Nat.le_of_lt"),
        ("  refine ⟨?_, ?_⟩", "refine", "⟨?_, ?_⟩"),
        ("  specialize h 3", "specialize", "h 3"),
    ] {
        let Tactic::Term(t) = one(body) else {
            panic!("{body} should take a term")
        };
        assert_eq!(t.name().unwrap().text(), name);
        assert_eq!(t.term().unwrap().text(), term);
    }
}

#[test]
fn refine_holes_are_synthetic_holes() {
    let Tactic::Term(t) = one("  refine ⟨?_, ?x⟩") else {
        panic!()
    };
    let holes = t
        .syntax()
        .descendants()
        .filter(|n| n.kind() == lean4_syntax::SyntaxKind::SYNTHETIC_HOLE)
        .count();
    assert_eq!(holes, 2);
}

#[test]
fn use_takes_a_term_list() {
    let Tactic::TermList(t) = one("  use 1, 2, 3") else {
        panic!("expected a term list")
    };
    let terms: Vec<String> = t.terms().map(|x| x.text()).collect();
    assert_eq!(terms, ["1", "2", "3"]);
}

// ---- patterns --------------------------------------------------------------

#[test]
fn intro_patterns_include_tuples() {
    let Tactic::Intro(intro) = one("  intro x _ ⟨a, b⟩") else {
        panic!("expected intro")
    };
    let pats: Vec<_> = intro.patterns().collect();
    assert_eq!(pats.len(), 3);
    assert_eq!(pats[0].name().unwrap().text(), "x");
    assert!(pats[1].is_hole());
    let nested: Vec<String> = pats[2]
        .parts()
        .map(|p| p.name().unwrap().text().to_string())
        .collect();
    assert_eq!(nested, ["a", "b"]);
}

#[test]
fn rintro_alternations_nest_inside_parentheses() {
    let Tactic::Intro(intro) = one("  rintro (hp | hq) hr") else {
        panic!()
    };
    assert_eq!(intro.patterns().count(), 2);
    assert_eq!(
        sexpr(intro.syntax()),
        "(TACTIC_INTRO rintro (RCASES_TUPLE ( (RCASES_ALT (RCASES_PAT hp) | (RCASES_PAT hq)) )) (RCASES_PAT hr))"
    );
}

// ---- cases-like ------------------------------------------------------------

#[test]
fn cases_with_alternatives_keeps_tactic_bodies() {
    let t = one("  induction n with\n  | zero => rfl\n  | succ k ih => simp");
    let Tactic::Cases(cases) = t else {
        panic!("expected induction")
    };
    let targets: Vec<String> = cases.targets().map(|x| x.text()).collect();
    assert_eq!(targets, ["n"]);

    let alts: Vec<_> = cases.alts().collect();
    assert_eq!(alts.len(), 2);
    // Each alternative's body is a real tactic sequence, not a token run.
    assert!(alts[0].tactics().is_some());
}

#[test]
fn rcases_with_patterns_is_distinguished_from_alternatives() {
    let Tactic::Cases(cases) = one("  rcases h with ⟨x, hx⟩ | ⟨y, hy⟩") else {
        panic!("expected rcases")
    };
    // The leading `h` is the target, not a pattern — that distinction is made
    // by tactic name, since position alone cannot resolve it.
    let targets: Vec<String> = cases.targets().map(|x| x.text()).collect();
    assert_eq!(targets, ["h"]);
    assert_eq!(cases.alts().count(), 0);
    assert_eq!(cases.patterns().count(), 1);
}

#[test]
fn induction_using_names_its_recursor() {
    let Tactic::Cases(cases) = one("  induction xs using List.rec") else {
        panic!()
    };
    assert_eq!(cases.using_term().unwrap().text(), "List.rec");
}

// ---- have-like -------------------------------------------------------------

#[test]
fn have_exposes_name_type_and_proof() {
    let Tactic::Have(have) = one("  have h : p ∧ q := ⟨hp, hq⟩") else {
        panic!("expected have")
    };
    assert_eq!(have.name().unwrap().text(), "have");
    assert_eq!(have.pattern().unwrap().name().unwrap().text(), "h");
    assert_eq!(have.ty().unwrap().text(), "p ∧ q");
    assert_eq!(have.value().unwrap().text(), "⟨hp, hq⟩");
}

#[test]
fn a_tactic_mode_have_may_omit_its_proof() {
    // Leaving off `:=` states the goal instead of proving it.
    let Tactic::Have(have) = one("  have h : p") else {
        panic!()
    };
    assert_eq!(have.ty().unwrap().text(), "p");
    assert!(have.value().is_none());
}

#[test]
fn obtain_leads_with_a_pattern() {
    let Tactic::Have(obtain) = one("  obtain ⟨n, hn⟩ : ∃ m, m > 0 := h") else {
        panic!("expected obtain to be have-like")
    };
    assert_eq!(obtain.name().unwrap().text(), "obtain");
    let parts: Vec<String> = obtain
        .pattern()
        .unwrap()
        .parts()
        .map(|p| p.name().unwrap().text().to_string())
        .collect();
    assert_eq!(parts, ["n", "hn"]);
    assert_eq!(obtain.value().unwrap().text(), "h");
}

#[test]
fn from_and_assignment_proofs_are_not_confused() {
    let Tactic::Have(s) = one("  suffices h : p from hp") else {
        panic!()
    };
    assert!(s.value().is_none(), "`from` is not `:=`");
    assert_eq!(s.from_term().unwrap().text(), "hp");
}

// ---- goal management -------------------------------------------------------

#[test]
fn case_names_a_goal_and_owns_a_block() {
    let Tactic::Case(case) = one("  case inl h => exact h") else {
        panic!("expected case")
    };
    let tags: Vec<String> = case.tags().map(|t| t.text().to_string()).collect();
    assert_eq!(tags, ["inl", "h"]);
    assert_eq!(case.tactics().unwrap().tactics().count(), 1);
}

#[test]
fn conv_records_location_and_selected_subterm() {
    let Tactic::Conv(conv) = one("  conv at h in a + 0 => rw [Nat.add_zero]") else {
        panic!("expected conv")
    };
    assert_eq!(
        conv.location()
            .unwrap()
            .hypotheses()
            .map(|h| h.text().to_string())
            .collect::<Vec<_>>(),
        ["h"]
    );
    assert_eq!(conv.pattern().unwrap().text(), "a + 0");
    assert_eq!(conv.tactics().unwrap().tactics().count(), 1);
}

#[test]
fn show_and_calc_work_in_tactic_position() {
    let Tactic::Show(show) = one("  show a + 0 = a") else {
        panic!("expected show")
    };
    assert_eq!(show.term().unwrap().text(), "a + 0 = a");

    let Tactic::Calc(_) = one("  calc a = b := h1\n    _ = c := h2") else {
        panic!("expected calc")
    };
}

// ---- combinators -----------------------------------------------------------

#[test]
fn combinators_own_an_inner_sequence() {
    for (body, name) in [
        ("  try simp", "try"),
        ("  repeat rfl", "repeat"),
        ("  all_goals simp", "all_goals"),
        ("  any_goals rfl", "any_goals"),
    ] {
        let Tactic::CombinatorApp(t) = one(body) else {
            panic!("{body} should be a combinator")
        };
        assert_eq!(t.name().unwrap().text(), name);
        assert!(t.tactics().is_some());
    }
}

#[test]
fn iterate_records_its_count() {
    let Tactic::CombinatorApp(t) = one("  iterate 3 rfl") else {
        panic!()
    };
    assert_eq!(t.count().unwrap().text(), "3");
}

#[test]
fn seq_focus_chains_tactics() {
    let Tactic::Chain(chain) = one("  constructor <;> simp") else {
        panic!("expected a <;> chain")
    };
    let names: Vec<String> = chain
        .tactics()
        .map(|t| t.name().unwrap().text().to_string())
        .collect();
    assert_eq!(names, ["constructor", "simp"]);
}

#[test]
fn focus_dots_and_first_alternatives_are_structured() {
    let all = tactics("  refine ⟨?_, ?_⟩\n  · exact hp\n  · exact hq");
    assert_eq!(all.len(), 3);
    assert!(matches!(all[1], Tactic::Focus(_)));
    assert!(matches!(all[2], Tactic::Focus(_)));

    let Tactic::Alt(alt) = one("  first\n    | exact hp\n    | simp") else {
        panic!("expected first")
    };
    assert_eq!(alt.alternatives().count(), 2);

    let Tactic::Bracketed(b) = one("  (simp; rfl)") else {
        panic!("expected a bracketed block")
    };
    assert_eq!(b.tactics().unwrap().tactics().count(), 2);
}

// ---- the fallback ----------------------------------------------------------

#[test]
fn unknown_tactics_still_parse_with_their_arguments_kept() {
    let Tactic::Generic(t) = one("  my_custom_tactic foo [bar] at h") else {
        panic!("an unrecognised tactic must fall back to the generic shape")
    };
    assert_eq!(t.name().unwrap().text(), "my_custom_tactic");
    assert_eq!(t.args().unwrap().text(), "foo [bar] at h");
}

#[test]
fn zero_argument_tactics_need_no_shape() {
    for body in ["  rfl", "  trivial", "  constructor", "  assumption"] {
        let Tactic::Generic(t) = one(body) else {
            panic!("{body} should use the generic shape")
        };
        assert!(
            t.args().is_none(),
            "a tactic with no arguments should carry no argument node"
        );
    }
}

#[test]
fn an_unknown_tactic_with_alternatives_keeps_its_blocks() {
    let Tactic::Generic(t) = one("  my_cases h with\n  | inl a => rfl\n  | inr b => rfl") else {
        panic!()
    };
    assert_eq!(t.alts().count(), 2);
}

// ---- layout is unaffected --------------------------------------------------

#[test]
fn structuring_tactics_did_not_break_nesting() {
    // The inner `by` must still end at the dedent rather than absorbing
    // `exact h`, now that `have` is a structured shape.
    let all = tactics("  have hp' : p := by\n    exact hp\n  exact ⟨hp', hq⟩");
    assert_eq!(all.len(), 2, "outer block should hold two tactics");
    assert!(matches!(all[0], Tactic::Have(_)));
    assert!(matches!(all[1], Tactic::Term(_)));
}
