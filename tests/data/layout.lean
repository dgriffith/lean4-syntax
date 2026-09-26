/-
Layout-sensitive forms reduced from mathlib. Each of these parsed in isolation
but failed in place, which is the signature of an indentation bug rather than a
missing rule.
-/
module

public import Mathlib.Tactic

@[expose] public section

variable {l : List Nat} {f g : Nat → Nat}

/-- A `have` whose body sits on the next line, inside a `match` alternative. -/
def normalize : Nat → Nat
  | 0 => 0
  | 1 =>
    match h : f 1 with
    | 0 => 1
    | _ => 2
  | n =>
    have ⟨t', ht'⟩ := pair n
    t'

/-- The same shape with `let`, and with the value being an application. -/
def viaLet (n : Nat) : Nat :=
  let ⟨a, b⟩ := pair n
  a

/-- `show` and `suffices` anchor the same way. -/
theorem anchored (p : Prop) (hp : p) : p := by
  suffices h : p by exact h
  show p
  exact hp

/-- A tactic sitting mid-line must not claim the next, dedented line. -/
theorem midline (a b : Nat) : a + b = b + a ∧ True := by
  simp only [Nat.add_comm]; intros
  constructor <;> (symm; assumption)

/-- `case` tags likewise. -/
theorem tags (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  case left => exact hp
  case right => exact hq

/-- Instance-introducing `let`/`have` variants take no name. -/
theorem instances (p : Prop) : True := by
  letI := Classical.propDecidable p
  haveI := Classical.dec p
  trivial

/-- Remaining arguments left to inference. -/
def inferred := f (g ..)

/-- Still a range, since there is no space. -/
def ranged := ∫ x in a..b, f x

/-- `haveI`/`letI` are identifiers, not keywords, but bind like `have`/`let`. -/
def instanceTerms : Nat :=
  haveI : Inhabited Nat := inferInstanceAs (Inhabited Nat)
  letI := Classical.propDecidable True
  0

/-- An operator section. -/
def section' := ((↑) : Nat → Int)

/-- Field abbreviation: `args` means `args := args`. -/
def abbreviated (cmd args env : Nat) := { cmd := cmd, args, env }

/-- Still a set literal, which shares this shape. -/
def setLit : Set Nat := {a, b}

/-- A decorated ASCII operator. -/
def decorated (x z : Nat) := x ~ᵤ z

@[deprecated (since := "2026-01-01")]
alias oldName := newName

/-- An ident-led command directly after an import must keep its own name. -/
deprecated_module (since := "2026-01-01")

end
