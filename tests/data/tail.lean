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

/-- Constructor docstrings come before the `|`, not after. -/
inductive Reachable : (Fin 6 → Nat) → Prop
  /-- The starting position. -/
  | base : Reachable 1
  /-- Remove a coin and add two. -/
  | move {B i} (rB : Reachable B) (hi : i < 5) :
      Reachable (B - single i 1)

/-- A universe level may be an expression, not only a name. -/
example : M.{w} R ⥤ A.{max u w} R where
  obj := f

/-- A measure-theoretic binder introduces its restriction with notation. -/
example := ∀ᵐ x ∂volume.restrict (Icc 0 1), p x

/-- Ascription with the type left to inference. -/
example := (f (g r) (_ : M) :)

/-- Matrix and vector notation. -/
example := AffineIndependent R ![A, B, C]

/-- An index may carry its in-bounds proof. -/
example := (p.cells[1]'p.one_lt).1

/-
Each bracketed form also appears as an *operand* below. A node kind the parser
produces but the typed `Term` enum omits is invisible to lowering, and shows up
only as a "missing operand" error — which needs the form to sit inside something
that expects a term. Twice now that gap has been found this way rather than by
reading the code.
-/
example := xs[n] + 1
example := ![A, B] = ys
example := (RatFunc k)⟦X⟧ → S
example := ‖x‖ + 1
example := Foo.{u} ≫ Bar.{v}
example := s!"{n}" ++ t

/-- A lambda may destructure a pair. -/
example := xs.map fun (a, b) => a + b

/-- A structure instance may draw on several sources. -/
example := { (f : A), (g f : B) with c := h f }

/-- Binders without a name. -/
example := fun k ↦ have {p} (pp : p.Prime) : p = 2 := by simp
  trivial

end
