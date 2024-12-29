import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Paperproof

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs
  -- we can use:
  -- apply mem_image_of_mem f xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · intro h x xs
    have h1 : f x ∈ f '' s
    · apply mem_image_of_mem f xs
    apply h
    apply h1
  intro h y ymem
  rcases ymem with ⟨x, xs, fxeq⟩
  rw [← fxeq]
  apply h
  apply xs

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  rintro x ⟨y, ys, yfeq⟩
  apply h at yfeq
  rw [← yfeq]
  apply ys

example : f '' (f ⁻¹' u) ⊆ u := by
  rintro x ⟨y, ys, yfeq⟩
  rw [← yfeq]
  apply ys

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro y yu
  rcases h y with ⟨x, xu⟩
  use x
  constructor
  · show f x ∈ u
    rw [xu]
    apply yu
  apply xu

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  rintro y ⟨x, xu, fxeq⟩
  use x
  constructor
  apply h xu
  apply fxeq

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  rintro x
  apply h

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  rfl

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  intro y ⟨x, ⟨xs, xt⟩, fxeq⟩
  constructor
  use x
  use x

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  intro y ⟨⟨x1, x1s, fx1s⟩, ⟨x2, x2t, fx2t⟩⟩
  use x1
  constructor
  · constructor
    apply x1s
    have h1 : x1 = x2
    apply h
    rw [fx1s, fx2t]
    rw [h1]
    apply x2t
  apply fx1s

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  intro y ⟨⟨x1, x1s, fx1eq⟩, h⟩
  use x1
  constructor
  · constructor
    apply x1s
    by_contra
    apply h
    use x1
  apply fx1eq


example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  rintro x ⟨h1, h2⟩
  show f x ∈ u \ v
  constructor
  apply h1
  apply h2


example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by

-- lol I should have used y but I am already in the second constructor statement
-- so oh well....
  ext y
  constructor
  · intro ⟨yfs, yv⟩
    rcases yfs with ⟨x, xs, fxy⟩
    use x
    · constructor
      · constructor
        apply xs
        rw [← fxy] at yv
        apply yv
      apply fxy
  intro ⟨x, ⟨⟨xs, xfv⟩ , fxy⟩⟩
  constructor
  use x
  rw [← fxy]
  apply xfv


example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  intro y ⟨x, ⟨⟨xs, xfu⟩, fxy⟩⟩
  constructor
  use x
  rw [← fxy]
  apply xfu

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  intro x ⟨xs, xfu⟩
  constructor
  · use x
  apply xfu


example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (xs | fxu)
  · left
    use x
  · right
    apply fxu


variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y
  simp
  constructor
  · rintro ⟨x, ⟨⟨i, xAi⟩ , fhy⟩⟩
    use i, x
  rintro ⟨i, x, xAi, fxy⟩
  use x
  constructor
  use i
  apply fxy

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro y
  simp
  intro x h fxy i
  use x
  constructor
  · apply h
  apply fxy

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro y
  simp
  intro h
  rcases h i with ⟨x, xAi, fxy⟩
  use x
  constructor
  · intro i'
    rcases h i' with ⟨x', x'Ai', fx'y⟩
    have h1 : f x = f x' := by
      rw [fxy, fx'y]
    have h2 : x = x' := by
      apply injf h1
    rw [h2]
    apply x'Ai'
  apply fxy

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  simp

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  simp

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x xpos y ypos
  intro e
  calc
    x = sqrt x ^ 2 := by rw [sq_sqrt xpos]
    _ = sqrt y ^ 2 := by rw [e]
    _ = y := by rw [sq_sqrt ypos]

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x xpos y ypos
  intro e
  dsimp at *
  calc
    x = sqrt (x ^ 2 ) := by rw [sqrt_sq xpos]
    _ = sqrt (y ^ 2) := by rw [e]
    _ = y := by rw [sqrt_sq ypos]


example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext y
  constructor
  · rintro ⟨x, ⟨xpos, rfl⟩⟩
    apply sqrt_nonneg
  intro ypos
  use y ^ 2
  constructor
  apply pow_nonneg ypos
  apply sqrt_sq
  apply ypos

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    dsimp at *
    apply pow_two_nonneg
  rintro ypos
  use sqrt y
  dsimp at *
  apply sq_sqrt ypos

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  · intro h y
    apply h
    apply inverse_spec
    use y
  intro h x1 x2 e
  rw [← h x1]
  rw [e]
  rw [h]

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  · intro h y
    apply inverse_spec
    apply h
  intro h y
  use inverse f y
  apply h

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := h₁
  have h₃ : j ∉ S := by rwa [h] at h₁
  contradiction

-- COMMENTS: TODO: improve this
end
