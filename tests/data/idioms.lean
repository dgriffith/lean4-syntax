prelude
import Init.Core
set_option autoImplicit false

open Nat List in
theorem opened : True := trivial

section Basics
variable (α β : Type) [BEq α]

notation:65 lhs " ⊕ " rhs:66 => Sum lhs rhs
infixl:70 " ⊗ " => Prod
prefix:max "√" => Nat.sqrt
postfix:max "⁺" => Nat.succ

macro_rules
  | `($x + $y) => `(Nat.add $x $y)

syntax "myTac" : tactic

declare_syntax_cat myCat

attribute [simp] Nat.add_zero Nat.zero_add

@[simp, norm_cast]
theorem cast_ok (n : Nat) : (n : Int) = n := by
  simp only [Int.ofNat_eq_coe] at *
  rfl

mutual
  def isEven : Nat → Bool
    | 0 => true
    | n + 1 => isOdd n

  def isOdd : Nat → Bool
    | 0 => false
    | n + 1 => isEven n
end

def withAux (n : Nat) : Nat := aux n + 1
  where
    aux : Nat → Nat
      | 0 => 0
      | k + 1 => k

def letRec : Nat → Nat := fun n =>
  let rec go : Nat → Nat
    | 0 => 0
    | k + 1 => go k
  go n

theorem combinators (p q : Prop) (hp : p) : p ∨ q := by
  first
    | exact Or.inl hp
    | exact Or.inr hp

theorem focus_dots (a b : Nat) : a + b = b + a ∧ True := by
  constructor
  · exact Nat.add_comm a b
  · trivial

theorem seq_focus (xs : List Nat) : True := by
  cases xs <;> simp_all

def destructure : Nat × Nat → Nat := fun ⟨a, b⟩ => a + b

def tryCatch : IO Unit := do
  try
    IO.println "hi"
  catch e =>
    IO.println (toString e)
  finally
    pure ()

#check @Nat.rec
#eval (1 + 2 : Nat)
#print axioms Nat.add

end Basics
