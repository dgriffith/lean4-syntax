import Mathlib.Tactic

variable {α : Type*} [DecidableEq α]

theorem simp_forms (a b : Nat) (h : a = b) (h2 : b = 0) : a + 0 = b := by
  simp only [Nat.add_zero, ← h, -h2, *] at h ⊢
  simp_all
  norm_num [Nat.succ_eq_add_one]
  simp (config := { decide := true }) [h]
  linarith [h, h2]
  omega

theorem rewrite_forms (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1, h2]
  rw [← h2] at h1 ⊢
  nth_rw 2 [h1]
  simp_rw [← h1]
  rwa [h1] at h2

theorem term_forms (p q : Prop) (hp : p) (hpq : p → q) : q := by
  apply hpq
  exact hp

theorem refine_holes (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  refine ⟨?_, ?_⟩
  · exact hp
  · exact hq

theorem intro_forms (p q : Prop) : p → q → p ∧ q := by
  intro hp hq
  constructor
  case left => exact hp
  case right => exact hq

theorem rintro_patterns (p q r : Prop) : (p ∨ q) → r → r := by
  rintro (hp | hq) hr
  · exact hr
  · exact hr

theorem cases_forms (n : Nat) (h : n = 0 ∨ n = 1) : True := by
  rcases h with rfl | rfl
  · trivial
  · trivial

theorem induction_with (n : Nat) : 0 ≤ n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ k ih =>
    exact Nat.le_succ_of_le ih

theorem induction_using (xs : List Nat) : xs.length ≥ 0 := by
  induction xs using List.rec with
  | nil => simp
  | cons x xs ih => simp

theorem obtain_forms (h : ∃ n : Nat, n > 0) : True := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨m, hm⟩ : ∃ m : Nat, m > 0 := ⟨1, Nat.one_pos⟩
  trivial

theorem have_forms (p : Prop) (hp : p) : p := by
  have h1 : p := hp
  have h2 := hp
  have : p := hp
  set q := p with hq
  replace h1 : p := hp
  suffices h3 : p from h1
  exact h1

theorem exists_forms : ∃ n : Nat, n > 0 := by
  use 1
  omega

theorem combinator_forms (a b : Nat) : a + b = b + a ∧ True := by
  constructor <;> simp [Nat.add_comm]
  all_goals try simp
  any_goals rfl
  first
    | exact trivial
    | simp
  repeat rfl

theorem conv_forms (a b : Nat) (h : a = b) : a + 0 = b := by
  conv_lhs => rw [Nat.add_zero]
  conv at h => rw [← Nat.add_zero]
  conv in a + 0 => rw [Nat.add_zero]
  exact h

theorem calc_tactic (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  calc a = b := h1
    _ = c := h2

theorem show_and_change (a : Nat) : a + 0 = a := by
  show a + 0 = a
  change a + 0 = a
  simp

theorem nested_blocks (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  refine ⟨?_, ?_⟩
  · have hp' : p := by
      exact hp
    exact hp'
  · exact hq

theorem unknown_tactics (n : Nat) : True := by
  my_custom_tac foo [bar] at h
  another_one <;> trivial
  trivial

-- A `cases`/`induction` target may name the case's defining equation.
example : P := by
  induction hg : g₁.support ∪ g₂.support
    using Finset.eraseInduction generalizing g₁ g₂ with
  | _ s ih =>
  obtain h | h := s.eq_empty_or_nonempty <;> subst s
  · simp_all
  simp only [ne_eq] at hf

example : P := by
  cases h : e with
  | zero => simp
  | succ n => simp

example : P := by
  induction n using Nat.rec with
  | zero => simp
example : P := by
  induction n generalizing m with
  | zero => simp

-- The tactic introducing a `with` is often mid-line while its alternatives are
-- back at the tactic block's column.
example : ∀ l : List M, op l.prod = (l.map op).reverse.prod := by
  intro l; induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.prod_cons, op_mul, ih]

-- `{ tac; tac }` groups tactics, which is how mathlib focuses a goal after
-- `refine ⟨?_, ?_⟩` and what `<;> { … }` applies to every goal.
example : P := by { simp }
example : P := by { intro h; exact h }
example : P := by constructor <;> { simp [h] }
example : P := by
  refine ⟨?_, ?_⟩
  { simp only [one_mul, inv_one, ← map_div, inv_inv] }
  { exact ite_eq_right (by simpa using h hs) }

-- A brace after `exact` or `refine` is still a structure instance, not a block.
example : P := by exact { f := 1 }
example : P := by refine { f := ?_ }
example : P := by simp; exact { toFun := f }

-- Lean allows a tactic between `with` and the alternatives, which then runs in
-- every branch.
example : P := by
  intro k
  induction k with intro i j hj hj'
  | zero =>
    simp only [add_zero] at hj
    rw [F.map'_self i]
  | succ k hk =>
    rw [← add_assoc] at hj
    subst hj

example : P := by
  induction n with
  | zero => simp
  | succ k ih => simp [ih]

-- `else`, `then` and `in` continue an enclosing *term*, so a `by` block inside
-- one ends before them. mathlib writes this 39 times, always across lines.
example (n : ℕ) (u v : V) : Finset (G.Walk u v) :=
  match n with
  | 0 =>
    if h : u = v then by
      subst u
      exact {Walk.nil}
    else ∅
  | n + 1 =>
    Finset.univ.biUnion fun (w : G.neighborSet u) => g n w v

example {v w : V} : ∀ (p : G.Walk v w) (u : V), u ∈ p.support → G.Walk u w
  | nil, u, h => by rw [mem_support_nil_iff.mp h]
  | cons r p, u, h =>
    if hx : v = u then by
      subst u
      exact cons r p
    else dropUntil p u <| by
      cases h

-- A tactic-mode `if` keeps its own `then`/`else`, and a term argument may
-- contain one.
example : P := by
  if h : c then simp else ring
example : P := by
  exact if h then a else b
