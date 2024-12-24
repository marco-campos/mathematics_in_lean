import MIL.Common
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic
import Paperproof

namespace C03S04

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y := by
  constructor
  -- Automatically finds an assumption to prove x ≤ y which in this case
  -- just applies h₀
  · assumption
  -- Assume the contradiction of h : x = y
  intro h
  apply h₁
  rw [h]

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  ⟨h₀, fun h ↦ h₁ (by rw [h])⟩

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  have h : x ≠ y := by
    contrapose! h₁
    rw [h₁]
  ⟨h₀, h⟩

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  rcases h with ⟨h₀, h₁⟩
  contrapose! h₁
  exact le_antisymm h₀ h₁

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩ h'
  exact h₁ (le_antisymm h₀ h')

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x :=
  fun ⟨h₀, h₁⟩ h' ↦ h₁ (le_antisymm h₀ h')

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  -- splits up h into two other hypothesis to apply directly.
  have ⟨h₀, h₁⟩ := h
  -- We need to prove y ≤ x implies not h0 and h1
  -- We are showing that if y ≤ x, then h0 will force x=y which contradicts h1
  contrapose! h₁
  -- h1 has been transformed so we now apply both h and h1 to show x = y
  exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h
  case intro h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h
  next h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  match h with
    | ⟨h₀, h₁⟩ =>
        contrapose! h₁
        exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  intro h'
  -- Splits the two components of the hypothesis from ∧
  apply h.right
  exact le_antisymm h.left h'

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x :=
  fun h' ↦ h.right (le_antisymm h.left h')

example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by
  -- Split the hypothesis
  have ⟨h₀, h₁⟩ := h
  -- Split the theorem into cases
  constructor
  -- case 1 is just the left hypothesis
  · apply h₀
  -- case 2 requires a negation so we prove using a contradiction.
  intro h'
  -- we will use the right assumption from the hypothesis so we show m=n
  -- follows from assuming n | m
  apply h₁
  -- Splits m = n into requiring n|m and m|n
  apply Nat.dvd_antisymm
  -- apply both the left hypothesis and the contradiction.
  apply h₀
  apply h'

example : ∃ x : ℝ, 2 < x ∧ x < 4 :=
  -- applies 5/2 to both expressions and proves it using norm_num
  ⟨5 / 2, by norm_num, by norm_num⟩

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y := by
  rintro ⟨z, xltz, zlty⟩
  exact lt_trans xltz zlty

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
  fun ⟨z, xltz, zlty⟩ ↦ lt_trans xltz zlty

example : ∃ x : ℝ, 2 < x ∧ x < 4 := by
  use 5 / 2
  -- This tells Lean to use norm_num on all the goals using the result.
  constructor <;> norm_num

example : ∃ m n : ℕ, 4 < m ∧ m < n ∧ n < 10 ∧ Nat.Prime m ∧ Nat.Prime n := by
  use 5
  use 7
  norm_num

example {x y : ℝ} : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩
  use h₀
  exact fun h' ↦ h₁ (le_antisymm h₀ h')

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y := by
  constructor
  · contrapose!
    rintro rfl
    rfl
  contrapose!
  exact le_antisymm h

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y :=
  ⟨fun h₀ h₁ ↦ h₀ (by rw [h₁]), fun h₀ h₁ ↦ h₀ (le_antisymm h h₁)⟩

example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y := by
  constructor
  · rintro ⟨h0, h1⟩
    constructor
    · apply h0
    intro h2
    apply h1
    rw [h2]
  rintro ⟨h3, h4⟩
  · constructor
    apply h3
    intro h5
    apply h4
    apply le_antisymm
    apply h3
    apply h5

theorem aux {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 :=
  --showing that x^2=0 since both x^2 and y^2 are ≥ 0
  have h' : x ^ 2 = 0 := by
    linarith [pow_two_nonneg x, pow_two_nonneg y]
  -- show x=0 by providing x^2 = 0
  pow_eq_zero h'

example (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h0
    constructor
    · apply aux h0
    rw [add_comm] at h0
    apply aux h0
  rintro ⟨rfl, rfl⟩
  linarith

section

example (x : ℝ) : |x + 3| < 5 → -8 < x ∧ x < 2 := by
  rw [abs_lt]
  intro h
  -- Remember you can just use this line of code to completely avoid
  -- having to rewrite the hypothesis.
  constructor <;> linarith

example : 3 ∣ Nat.gcd 6 15 := by
  rw [Nat.dvd_gcd_iff]
  constructor <;> norm_num

end

theorem not_monotone_iff {f : ℝ → ℝ} : ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y := by
  rw [Monotone]
  push_neg
  rfl

example : ¬Monotone fun x : ℝ ↦ -x := by
  rw [not_monotone_iff]
  use 0, 1
  constructor <;> linarith

section
variable {α : Type*} [PartialOrder α]
variable (a b : α)

example : a < b ↔ a ≤ b ∧ a ≠ b := by
  rw [lt_iff_le_not_le]
  constructor
  · rintro ⟨h0, h1⟩
    constructor
    · apply h0
    intro h2
    apply h1
    rw [h2]
  rintro ⟨h3, h4⟩
  · constructor
    · apply h3
    intro h5
    apply h4
    apply le_antisymm
    apply h3
    apply h5

end

section
variable {α : Type*} [Preorder α]
variable (a b c : α)

example : ¬a < a := by
  rw [lt_iff_le_not_le]
  push_neg
  intro h
  apply h

example : a < b → b < c → a < c := by
  simp only [lt_iff_le_not_le]
  rintro ⟨h0, h1⟩ ⟨h2, h3⟩
  constructor
  · apply le_trans h0 h2
  intro h
  apply h1
  apply le_trans h2 h

end
