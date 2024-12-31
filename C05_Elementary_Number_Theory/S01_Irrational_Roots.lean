import MIL.Common
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Paperproof

#print Nat.Coprime

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 :=
  h

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 := by
  rw [Nat.Coprime] at h
  exact h

example : Nat.Coprime 12 7 := by norm_num

example : Nat.gcd 12 8 = 4 := by norm_num

#check Nat.prime_def_lt

example (p : ℕ) (prime_p : Nat.Prime p) : 2 ≤ p ∧ ∀ m : ℕ, m < p → m ∣ p → m = 1 := by
  rwa [Nat.prime_def_lt] at prime_p

#check Nat.Prime.eq_one_or_self_of_dvd

example (p : ℕ) (prime_p : Nat.Prime p) : ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p :=
  prime_p.eq_one_or_self_of_dvd

example : Nat.Prime 17 := by norm_num

-- commonly used
example : Nat.Prime 2 :=
  Nat.prime_two

example : Nat.Prime 3 :=
  Nat.prime_three

#check Nat.Prime.dvd_mul
#check Nat.Prime.dvd_mul Nat.prime_two
#check Nat.prime_two.dvd_mul

theorem even_of_even_sqr {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  cases h <;> assumption

example {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m :=
  Nat.Prime.dvd_of_dvd_pow Nat.prime_two h

example (a b c : Nat) (h : a * b = a * c) (h' : a ≠ 0) : b = c :=
  -- apply? suggests the following:
  (mul_right_inj' h').mp h

example {m n : ℕ} (coprime_mn : m.Coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
-- Suppose by contradiction that m ^ 2 = 2 * n ^ 2. We will show that 2 | 1 which
-- gives the contradiction.
  intro sqr_eq
  -- First, notice 2 | 2 * n ^ 2, then 2 | m ^ 2 by the assumption so
  -- 2 | m by an application of even_of_even_sqr
  have h : 2 ∣ m := by
    apply even_of_even_sqr
    rw [sqr_eq]
    apply Nat.dvd_mul_right

  -- this splits the division tactic by introducing the existence of such a k
  -- such that the equality holds.
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp h

  -- We can now write m = 2 * k and substitution into the assumption gives:
  -- 2 * (2 * k ^ 2) = 2 * n ^ 2 which simplifies to (2 * k ^ 2) = n ^ 2
  have h1 : 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring

  have h2 : 2 * k ^ 2 = n ^ 2 := by
    -- we need norm_num here as it is the only way we can guarantee
    -- that the condition of 2 > 0 will be satisfied without introducing a
    -- new hypothesis.
    apply Nat.eq_of_mul_eq_mul_left (by norm_num) h1

  -- Then 2 | n by another application of even_of_even_sqr to 2 * k ^ 2 = n ^ 2.
  have h3 : 2 ∣ n := by
    apply even_of_even_sqr
    rw [← h2]
    apply Nat.dvd_mul_right

  -- If 2 | m and 2 | n, then 2 | m.gcd n.
  have h4 : 2 ∣ m.gcd n := by
    apply Nat.dvd_gcd
    apply h
    apply h3

  -- m.gcd n = 1 since they are coprime so this implies 2 | 1, a contradiction.
  have h5 : 2 ∣ 1 := by
  -- allows us to introduce one of our earlier tactics but with the variable switched.
  -- and we must then show that m.gcd n = 1
    convert h4
    symm
    exact coprime_mn
  norm_num at h5

example {m n p : ℕ} (coprime_mn : m.Coprime n) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq

  have h : p ∣ m := by
    apply prime_p.dvd_of_dvd_pow
    rw [sqr_eq]
    apply dvd_mul_right

  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp h

  have h1 : p * (p * k ^ 2) = p * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring

  have h2 : p * k ^ 2 = n ^ 2 := by
    apply (mul_right_inj' _).mp h1
    exact prime_p.ne_zero

  have h3 : p ∣ n := by
    apply prime_p.dvd_of_dvd_pow
    rw [← h2]
    apply Nat.dvd_mul_right

  have h4 : p ∣ m.gcd n := by
    apply Nat.dvd_gcd
    apply h
    apply h3

  have h5 : p ∣ 1 := by
  -- allows us to introduce one of our earlier tactics but with the variable switched.
  -- and we must then show that m.gcd n = 1
    convert h4
    symm
    exact coprime_mn

  have h6 : 2 ≤ 1 := by
    apply prime_p.two_le.trans
    exact Nat.le_of_dvd zero_lt_one h5

  norm_num at h6

-- Lists out the prime factors of a number
#check Nat.primeFactorsList
-- If p is found in the prime factors list, then p must be prime
#check Nat.prime_of_mem_primeFactorsList
#check Nat.prod_primeFactorsList
#check Nat.primeFactorsList_unique

theorem factorization_mul' {m n : ℕ} (mnez : m ≠ 0) (nnez : n ≠ 0) (p : ℕ) :
    (m * n).factorization p = m.factorization p + n.factorization p := by
  rw [Nat.factorization_mul mnez nnez]
  rfl

theorem factorization_pow' (n k p : ℕ) :
    (n ^ k).factorization p = k * n.factorization p := by
  rw [Nat.factorization_pow]
  rfl

theorem Nat.Prime.factorization' {p : ℕ} (prime_p : p.Prime) :
    p.factorization p = 1 := by
  rw [prime_p.factorization]
  simp

example {m n p : ℕ} (nnz : n ≠ 0) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have nsqr_nez : n ^ 2 ≠ 0 := by simpa
  have eq1 : Nat.factorization (m ^ 2) p = 2 * m.factorization p := by
    rw [Nat.factorization_pow]
    rfl
  have eq2 : (p * n ^ 2).factorization p = 2 * n.factorization p + 1 := by
    rw [Nat.factorization_mul]
    · rw [prime_p.factorization]
      rw [Nat.factorization_pow]
      simp
      ring
    · apply prime_p.ne_zero
    apply nsqr_nez

  have : 2 * m.factorization p % 2 = (2 * n.factorization p + 1) % 2 := by
    rw [← eq1, sqr_eq, eq2]
  rw [add_comm, Nat.add_mul_mod_self_left, Nat.mul_mod_right] at this
  norm_num at this

example {m n k r : ℕ} (nnz : n ≠ 0) (pow_eq : m ^ k = r * n ^ k) {p : ℕ} :
    k ∣ r.factorization p := by
  rcases r with _ | r
  · simp
  have npow_nz : n ^ k ≠ 0 := fun npowz ↦ nnz (pow_eq_zero npowz)
  have eq1 : (m ^ k).factorization p = k * m.factorization p := by
    rw [Nat.factorization_pow]
    rfl
  have eq2 : ((r + 1) * n ^ k).factorization p =
      k * n.factorization p + (r + 1).factorization p := by
    rw [factorization_mul' r.succ_ne_zero npow_nz]
    rw [factorization_pow', add_comm]

  have : r.succ.factorization p = k * m.factorization p - k * n.factorization p := by
    rw [← eq1, pow_eq, eq2, add_comm, Nat.add_sub_cancel]
  rw [this]
  apply Nat.dvd_sub' <;>
  apply Nat.dvd_mul_right


#check multiplicity
