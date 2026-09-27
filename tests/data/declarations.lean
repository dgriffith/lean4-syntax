/-! # A module docstring -/
import Lean.Data.HashMap
import Std

namespace Demo

universe u v

variable {α : Type u} [Inhabited α]

/-- A binary tree. -/
inductive Tree (α : Type u) where
  | leaf
  | node (l : Tree α) (v : α) (r : Tree α)
  deriving Repr, BEq

structure Point where
  x : Float := 0.0
  y : Float := 0.0
  deriving Inhabited

class Container (f : Type u → Type v) where
  empty : f α
  insert : α → f α → f α

@[simp]
theorem add_zero (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp [Nat.add_succ, ih]

private def size : Tree α → Nat
  | .leaf => 0
  | .node l _ r => size l + size r + 1

def Tree.mirror : Tree α → Tree α
  | .leaf => .leaf
  | .node l v r => .node (mirror r) v (mirror l)

theorem nested_by (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  have hp' : p := by
    exact hp
  exact ⟨hp', hq⟩

def sumList (xs : List Nat) : Nat :=
  xs.foldl (fun acc x => acc + x) 0

def main : IO Unit := do
  let mut total := 0
  for i in [0:10] do
    total := total + i
  if total > 20 then
    IO.println s!"big {total}"
  else
    IO.println "small"
  let stdin ← IO.getStdin
  let line ← stdin.getLine
  IO.println line

example : ∀ x : Nat, x ≤ x + 1 := fun x => Nat.le_succ x

noncomputable def choice_fn : (α → Prop) → α := fun _ => default

instance : Add Point where
  add a b := ⟨a.x + b.x, a.y + b.y⟩

def descr (t : Tree α) : String :=
  match t with
  | .leaf => "leaf"
  | .node _ _ _ => "node"

abbrev NatPred := Nat → Prop

theorem calc_demo (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c :=
  calc a = b := h1
    _ = c := h2

end Demo

/-- `class inductive` has a constructor list, not a field list. -/
class inductive IsGCDMonoid (α : Type*) [CommMonoidWithZero α] : Prop
  | intro : GCDMonoid α → IsGCDMonoid α

class inductive Reachable (α : Type) : Prop where
  /-- The starting position. -/
  | base : Reachable α
  | step : Reachable α → Reachable α

/-- A `where` field may be defined by equations rather than by a value, exactly
as a `def` may, and several such fields can follow one another. -/
instance : Add N₃ where
  add
  | 0, x => x
  | x, 0 => x
  | 1, 1 => two
  | _, _ => more

protected def map : h.cochainComplex ⟶ h'.cochainComplex where
  f
  | .ofNat n => fL.f n
  | .negSucc n => fK.f n
  comm'
  | .ofNat i, _, .refl _ => fL.comm _ _
  | .negSucc i, _, .refl _ => fK.comm _ _

instance : Foo where
  a := 1
  b := 2

/-- Several pattern groups may share one body. -/
def with_shared_bodies : WithTop α → WithTop α → Prop
  | ⊤, ⊤ | ⊤, (b : α) => le_rfl
  | 0 | 1 => trivial
  | _, _ => h
