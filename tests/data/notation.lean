/-
Notation drawn from mathlib, reduced. The curated forms need real rules; the
rest go through the generic symbol fallback.
-/
module

public import Mathlib.Analysis.Normed.Group.Basic

@[expose] public section

variable {R M N α β : Type*} {s t : Set α} {f : α → β}

-- Curated delimiter pairs.
example (x : M) := ‖x‖
example (x : M) := ‖x‖₊
example (r : ℝ) := ⌊r⌋
example (r : ℝ) := ⌈r⌉
example (x y : M) := ⟪x, y⟫
example (x y : M) := ⁅x, y⁆

-- Curated operators, at Lean's precedences.
example (f g h : α → α) := f ≫ g ≫ h
example (X Y : α) := X ⟶ Y
example (C D : α) := C ⥤ D
example (r : R) (x : M) := r • x
example (a b : Nat) := a ≡ b
example := f '' s
example := f ⁻¹' t

-- Big operators bind variables, like quantifiers do.
example (g : Nat → Nat) := ∑ i, g i
example (g : Nat → Nat) := ∑ i ∈ s, g i
example (g : Nat → Nat) := ∏ i ∈ s, g i
example (g : Nat → Nat) := ⨆ i, g i
example (g : Nat → Nat) := ⋃ i, g i
example (g : Nat → Nat) := ∫ x, g x

-- Constants are atoms, so they may be applied or passed.
example := (⊤ : Set α)
example := (⊥ : Set α)
example := (∅ : Set α)
example (X : α) := 𝟙 X

-- Decorated operators and type names are single tokens.
example (M N : Type) := M →ₗ[R] N
example (M N : Type) := M ⊗[R] N
example := (Nat → Nat) →+ Nat
example (n : ℕ+) : ℕ+ := n
example (x : ℝ≥0∞) : ℝ≥0∞ := x

-- Postfix modifiers.
example := sᶜ
example (C : Type) := Cᵒᵖ

-- Notation with no rule of its own still parses, at an assumed precedence.
example (a b : Nat) := a ⊸ b
example (K : Type) := Kᗮ

-- Core syntax the notation work surfaced.
example (g : Nat → Nat → Nat) := g (a := 1) (b := 2)
example (ha hb : Nat) := congr($ha + $hb)

end
