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

/-- A filter modifier is a bare operator in brackets, not a term. -/
theorem nhds_within_forms (hp : HasFPowerSeriesAt f p z₀) :
    ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0 := by
  simp

example : ∀ᶠ r : ℝ≥0∞ in 𝓝[>] 0, P r := by simp
example : 𝓝[<] a ≤ 𝓝[≤] a := le_rfl

-- These must keep their existing readings: a list argument, an index, a
-- tensor product, and a continuous-linear-map arrow.
example := f [a, b]
example := xs[i]?
example : M ⊗[R] N := x
example : E →L[𝕜] F := f

/-- Set-image notation ascribes the bound variable to the right of the bar. -/
example := {f i | i : ι}
example := {(b₁.h i, b₂.h (eι i)) | i : ι₁}
example := {(i, j) | i : ι, j : κ}
example := {f i j | (i : ι) (j : κ)}

-- Every other reading of a brace has to survive that: set-builder, subtype,
-- set literal, structure instance, and `with`-update.
example := {x | p x}
example := {x : T | p x}
example := {x ∈ s | p x}
example := {a, b, c}
example := {x // p x}
example := { s with f := 1 }
example := { f := 1, g := 2 }

/-- mathlib declares operators the parser cannot know about, so a run of
operator characters is one token: list suffix and prefix, Kleisli composition,
and friends. -/
example := a <:+ b
example := a <+: b
example := a <:+: b
example := f >=> g
example := a <&&> b
example := a ^^^ b
example := a &&& b
example := xs <+ ys
example := a ==> b
example := {l | ∀ l₂, l₂ ≠ [] → l₂ <:+ l → 0 < l₂.sum}

-- The run must not swallow a comment start, must not begin at a `|`, and must
-- not disturb the operators that were already tokens.
def pipe_arms : Nat → Nat
  | 0 => 1
  | -1 => 2
  | n + 1 => n
example := ‖-x‖
example := ⟨a, -b⟩
example := [-1, 2]
example := a * -b
example := f <| -x
example := a <|> b
example := a >>= f
example := g <$> a
example := x |>.foo
example := s.map (· + 1)

/-- A string literal may span lines; mathlib's expected-message tests rely on
it. The blank line and the goal state below are inside the literal. -/
example : True := by
  success_if_fail_with_msg
    "Tactic `gcongr` failed: there is no `@[gcongr]` lemma.

x y : ℕ
⊢ f x ≤ f y"
    (gcongr f ?a)
  trivial

/-- A pattern-matching `let` in `do` may give its failure branch inline. -/
example : m Nat := do
  let some value := nonEmptyEnvValue value? | return ifUnset
  let some scope ← getRepoScope | return false
  return 0

-- The else-branch must not swallow a following match alternative: a `|` back
-- at the arm's own column belongs to the `match`.
example (x : Option Nat) : m Nat := do
  match x with
  | some y => do
    let z := y
    pure z
  | none => pure 0

/-- Structure-instance and `where` bodies may separate fields with `;`. -/
def of : α →ₙ* AssocQuotient α where toFun := Quot.mk _; map_mul' _x _y := rfl

def g : H →* G where
  toFun := ((↑) : H → G); map_one' := rfl; map_mul' := fun _ _ => rfl

example := { f := 1; g := 2 }

/-- A `match` in statement position inside `do` gives each arm a do sequence,
so an arm can run several statements. -/
example (b : B) : m Unit := do
  let x ← g
  match b with
  | .azure =>
    let t ← getAzureAuth
    azurePutStaged t x
  | .s3 =>
    let c ← getS3Auth
    s3PutStaged c x

-- A `where` field's value may begin on the next line, to the left of the field
-- name, and an arm's `do` body need only line up with itself.
meta def evalAbv : PositivityExt where eval {_ _α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  let (.app f a) ← whnfR e | throwError "not abv"
  let pa' ← mkAppM ``abv_nonneg #[f, a]
  pure (.nonnegative pa')

-- A `where` field's value may also start mid-line and continue *below* its own
-- first token. Anchoring a block on that first token must only ever lower the
-- indentation threshold, never raise it.
instance : Foo where
  monotone' := monotone_iff_forall_lt.2 (by
    simp)
  total h := sub_eq_zero.mp <| epsilon_total fun i ↦ by
    simp

-- A `where` field's value may start on the next line at exactly its field's own
-- column. The threshold is then that column, so the *next* field is not read as
-- one more argument of the value.
instance punit_algebra : Algebra R PUnit.{v + 1} where
  algebraMap :=
  { toFun _ := PUnit.unit
    map_one' := rfl
    map_mul' _ _ := rfl }
  commutes' _ _ := rfl
  smul_def' _ _ := rfl

/-- A parenthesized binder may destructure instead of naming, with the type
ascription applying to the pattern. -/
example := (fun (⟨g, g'⟩ : presB.G × presM.R) ↦ presB.var g • Finsupp.single g' (1 : B))

/-- A structure instance may name the structure being built, where the fields
alone would leave it to be inferred. -/
example := { f := 1 : T }
example := { f := 1, g := · : T }
example := ⟨({ toLinearMap := ofClass f, norm_map' := · : E →ₗᵢ[𝕜] E' }.inner_map_map), h⟩

/-- `⁻¹` is a token in its own right, so a symbol before it must not swallow it:
`n !⁻¹` is the inverse of the factorial, not one operator called `!⁻¹`. -/
example := n !⁻¹
example := (n !⁻¹ : 𝕂) • ContinuousMultilinearMap.mkPiAlgebraFin 𝕂 n 𝔸

/-- A `|` never takes a decoration, because it closes `|x|`: the multiplicative
absolute value is `|x|` with `ₘ` applied to it. -/
example : |x|ₘ ∈ H ↔ x ∈ H := by simp

-- The forms that decoration exists for must keep working.
example := f ⁻¹' s
example := x⁻¹
example := (f : E →ₗ[R] F)
example := a =ᵐ[μ] b
example := |x|
def factorial_arms : Nat → Nat
  | 0 => 1
  | n + 1 => n
