/-
Constructs taken from real mathlib files, reduced. Every one of these was a
parse failure found by `examples/corpus_report.rs`; they are kept here so the
corpus test catches a regression.
-/
module

public import Mathlib.Order.Basic
public meta import Mathlib.Tactic.ToDual
meta import Mathlib.Tactic.Common
import Mathlib.Data.Nat.Defs

/-! Module docstring after the imports. -/

@[expose] public section

noncomputable section

assert_not_exists Finset

alias foo := Nat.succ

open Function Set
export Nat (succ pred)

section Scoped
variable {β : Type}
include β
omit β

nonrec def nonRecursive : Nat := 0
end Scoped

variable {α : Type*} [Inhabited α]

variable (α) in
/-- A declaration scoped to the preceding `variable ... in`. -/
noncomputable abbrev dim := 0

structure Bundled (G H : Type*) where
  /-- Doc comments attach to fields. -/
  protected toFun : G → H
  /-- A field may take arguments of its own. -/
  bound (i : Nat) : i ≤ i
  ac : Nat
  rs : Nat → Nat

public def visible : Nat := 0

meta def metaLevel : Nat := 1

instance : Inhabited (Bundled Nat Nat) :=
  ⟨{  toFun := id
      bound := fun _ => Nat.le_refl _
      ac := 0
      rs := fun _ => 0 }⟩

example : 1 < 3 := by
  exact (show 1 < 3 by omega)

theorem coercions (n : Nat) (f : Nat → Nat) : ↑n = ↑n ∧ ⇑f = ⇑f := by
  constructor <;> rfl

def arrays : Array Nat := #[1, 2, 3]

def emptyArray : Array Nat := #[]

theorem suffices_by (p : Prop) (hp : p) : p := by
  suffices h : p by exact h
  exact hp

end

end
