//! The invariant the whole design rests on: the tree reproduces the source.
//!
//! This must hold for *every* input, including ones that fail to parse, since
//! unparsable tokens are wrapped in `ERROR` nodes rather than dropped.

/// Every sample must round-trip exactly, and the tree's extent must cover the
/// whole file.
fn assert_roundtrips(src: &str) {
    let parse = lean4_syntax::parse(src);
    assert_eq!(
        parse.text(),
        src,
        "tree text differs from source\n--- tree ---\n{}",
        lean4_syntax::syntax::debug_tree(&parse.syntax())
    );
    assert_eq!(
        u32::from(parse.syntax().text_range().end()) as usize,
        src.len(),
        "tree does not span the whole source"
    );
}

#[test]
fn well_formed_declarations() {
    for src in [
        "def f := 1",
        "def f (n : Nat) : Nat := n + n\n",
        "theorem t : True := trivial",
        "@[simp] private theorem t : True := trivial",
        "/-- doc -/\ndef f := 1",
        "structure P where\n  x : Nat\n  y : Nat\n",
        "inductive T where\n  | leaf\n  | node (l : T) (r : T)\n",
        "instance : Add Nat where\n  add a b := a + b\n",
        "abbrev N := Nat",
        "example : True := trivial",
        "axiom choice : ∀ {α : Type}, Nonempty α → α",
        "class C (α : Type) where\n  f : α → α\n",
    ] {
        assert_roundtrips(src);
    }
}

#[test]
fn terms_of_every_shape() {
    for src in [
        "def f := fun x => x",
        "def f := λ x ↦ x",
        "def f := ∀ x : Nat, x = x",
        "def f := ∃ x > 0, x = x",
        "def f := let x := 1; x",
        "def f := have h : True := trivial; h",
        "def f := if h : c then a else b",
        "def f := ⟨1, 2, 3⟩",
        "def f := { x := 1, y := 2 }",
        "def f := { s with x := 1 }",
        "def f := { x : Nat // x > 0 }",
        "def f := { x | x > 0 }",
        "def f := [1, 2, 3]",
        "def f := (1, 2)",
        "def f := (x : Nat)",
        "def f := x.1.2",
        "def f := (g x).field",
        "def f := x |>.foo",
        "def f := @Nat.succ",
        "def f := a ∘ b ∘ c",
        "def f := xs.map fun x => x + 1",
        "def f := match x with | 0 => a | n + 1 => b",
        "def f := do\n  let x ← m\n  pure x\n",
        "def f := by simp",
        "def f := Foo.{u, v}",
        "def f := s!\"interpolated {x}\"",
        "def f := `(term| foo)",
    ] {
        assert_roundtrips(src);
    }
}

#[test]
fn malformed_input_still_round_trips() {
    for src in [
        "",
        "   \n\n  ",
        "def",
        "def f :=",
        "def f := )",
        "def f := ((((",
        ":= := :=",
        "/- unterminated comment",
        "\"unterminated string",
        "def f := 1\n@#$%^\ndef g := 2",
        "theorem t : p := by\n",
        "⟨⟩⟨⟩",
        "λ",
        "\u{1f600}",
    ] {
        assert_roundtrips(src);
    }
}

#[test]
fn comments_and_whitespace_are_preserved_everywhere() {
    let src = "\
-- leading line comment
/- block -/ def /- inside -/ f /- after name -/ := /- before value -/ 1 -- trailing

/-! module doc -/

/- final -/
";
    assert_roundtrips(src);
}

#[test]
fn crlf_and_unicode_survive() {
    assert_roundtrips("def f := 1\r\ndef g := 2\r\n");
    assert_roundtrips("def α : Type := β\n");
    assert_roundtrips("def «weird name» := 1\n");
}
