import MIL.Common
import Mathlib.Data.Real.Basic
import Paperproof

namespace C03S03

section
variable (a b : ℝ)

example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)

example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  intro fnlb
  rcases fnlb with ⟨a, fnlba⟩
  rcases h a with ⟨x, hx⟩
  have : a ≤ f x := fnlba x
  linarith

theorem ex3_3 : ¬FnHasUb fun x ↦ x := by
  -- introduce the statement that you want to contradict
  intro fub
  rcases fub with ⟨a, fuba⟩
  -- declare the has upper bound with a specific input.
  -- We have a new variable a which is the upper bound from FnHasUb
  -- and a hypothesis fuba which says we have this property.
  have : a + 1 ≤ a := fuba (a+1)
  -- The calculation here is the contradiction which is constructed
  -- by the hypothesis.
  linarith

#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)

example (h : Monotone f) (h' : f a < f b) : a < b := by
  -- changes the goal to prove ¬a>b
  apply lt_of_not_ge
  -- introduce the goal of proving False for a > b
  intro h''
  -- we want to contradict the hypothesis so we must show f a ≥ f b
  apply absurd h'
  -- goal is currently ¬ f a < f b, so we apply not_lt_of_ge
  -- and we must show f a ≥ f b
  apply not_lt_of_ge
  -- apply monotonicity
  apply h
  -- apply the contradicting goal h''
  apply h''

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  -- introduces the goal to prove false for f being monotone.
  intro monf
  -- want to show that ¬ f b < f a
  apply absurd h'
  -- will show that f b ≥ f a
  apply not_lt_of_ge
  -- monotinicity assumption recovers b ≤ a
  apply monf
  -- applying h gives the contradiction.
  apply h

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by
    intro a b leaf
    rfl
  have h' : f 1 ≤ f 0 := le_refl _
  have : (1: ℝ) ≤ 0 := h monof h'
  linarith

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro h'
  -- If we write the proof this way, then we take ε = x,
  -- and then we use the fact that x > 0 from h'.
  have h'' := h x h'
  -- we can now finish the contradiction.
  linarith
end

section
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro x Px
  apply h
  use x

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  -- introduce the negation
  intro negxPx
  -- you state the negation using the assumtion of x with Px
  rcases negxPx with ⟨x, Px⟩
  -- apply the hypothesis for this x which gives ¬ P x
  apply h x
  -- contradiction.
  apply Px

-- Note: This one is not in the solutions! It's also a bit weird.
example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  sorry


example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  -- introduce the negation of for all x, Px
  intro h'
  -- Here we are showing this for the case of a particular x, nPx := ¬ P x
  rcases h with ⟨x, nPx⟩
  -- Goal is to resolve nPx as False
  apply nPx
  -- h' with the given x gives us Px, a contrdiction.
  apply h' x

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩

example (h : ¬¬Q) : Q := by
  by_contra h'
  apply h
  apply h'

example (h : Q) : ¬¬Q := by
  by_contra h'
  apply h'
  apply h

end

section
variable (f : ℝ → ℝ)

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  -- Let a
  intro a
  -- Suppose there does not exists x such that f(x) > a
  by_contra h'
  -- f does not have an upper bound, we will show it does.
  apply h
  -- then for all x, f(x) > a
  use a
  intro x
  -- generating the contradiction so we want to show ¬ f x > a
  apply le_of_not_gt
  -- introduce the new hypothesis that f x > a
  intro h''
  -- apply h' since this says that ¬ ∃ x, fx > a
  -- so the new goal is to show ¬ ∃ x
  apply h'
  -- apply the x to generate the contradiction.
  use x


example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  -- here they are just expanding the definitions to then use push_neg
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h

example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  -- upack the definition of monotone, push the negation, apply h.
  dsimp only [Monotone] at h
  push_neg at h
  exact h


-- The following example is the same as the earlier one. So you can
-- initialize the contraposition and apply h all at once.
example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  -- contrapose transposes A → B to ¬B → ¬A
  -- The ! after contrapose applies push_neg immediately
  contrapose! h
  exact h

-- Here the hypothesis is A → B so ∀ ε > 0 → x ≤ ε
-- but the hypothesis transforms this to ∃ ε > 0 such that ε < x
-- via the negation as well.
example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith

end

section
variable (a : ℕ)

example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction

end
