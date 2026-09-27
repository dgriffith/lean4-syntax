/-
Forms from the mathlib parse tail (#17), reduced. Each was among the largest
remaining causes measured by `examples/corpus_report.rs`.
-/
module

public import Mathlib.Tactic

@[expose] public section

variable {s t : Set Nat} {x : Nat} {f g : Nat → Nat} {m n : Nat}

/-- Absolute value, whose `|` collides with the match-alternative separator. -/
example := |x|
example := sqrt (2 * x - 1) + |sqrt (2 * x - 1) - 1|
example := f |x| + g |x|

/-- And the structural uses of `|` still work alongside it. -/
def alternatives : Nat → Nat
  | 0 => 1
  | k + 1 => k

def setBuilder : Set Nat := {y | y > 0}

example : True := by
  rcases h with a | b
  · trivial
  · trivial

example : True := by
  first
    | exact h
    | trivial

/-- Set difference. -/
example := s \ t

/-- Factorial, after a bracket and across whitespace. -/
example := (n - 1)!
example := n !

/-- A coercion in argument position. -/
example := P n ↑m ↑n

/-- Nested numeric projections: `2.2` is two of them, not a float. -/
example := (f x).2.2

/-- Indexing, told apart from a list argument by adjacency. -/
example := xs[n]
example := xs[n]?
example := xs[n]!
example := f [n, n]

-- A docstring before a `#` command, and an `in` clause on it.
/-- info: 12 -/
#guard_msgs in
#norm_num (12 : Nat)

-- An attribute whose body continues at column 0.
/-- doc -/
@[to_additive
/-- additive doc -/]
lemma tagged (h : p) : p := h

/-- `extends` after the result type, which is the reverse of the usual order. -/
structure Sub (R : Type u) : Type u
    extends Add R where
  mem : Nat

/-- A notation scoped to another namespace, with an attribute ahead of it. -/
@[inherit_doc] scoped[Veroff] infixl:70 " ⊚ " => Veroff.f

/-- Postfix notation binds tighter than application, so `ˣ` belongs to `ℤ`. -/
example := P (g ℕ ℤˣ ℤ fun i => (w i).s)

/-- Composition of isomorphisms, and absolute continuity. -/
example := e ≪≫ f
example := μ ≪ ν

/-- A bound variable may carry several restrictions. -/
example := ∑ p ∈ G with Easy p, f p

/-- One tactic per goal rather than the same tactic to all of them. -/
example : True := by
  constructor <;> [skip; trivial]

/-- An interpolated string whose embedded term contains a string. -/
example := s!"one of {", ".intercalate names}"
example := "{"

end
