/-
Copyright (c) 2025 Alessandro Iraci. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.Ring.Regular
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.Tactic

/-!
# q-analogs

The q-analog of a theorem, identity or expression is a generalization involving a new parameter q
that returns the original theorem, identity or expression in the limit as q → 1.
For example, the q-analog of a natural number n, denoted [n]_q, is the sum 1 + q + ... + q^(n-1).

## Main definitions

For R a commutative semiring, and q : R,

* `qNat n q` is the q-analog of the natural number `n`, defined as `1 + q + ... + q^(n-1)`.
* `qFactorial n q` is the product of the q-naturals up to `n`.
* `qBinomial n k q` is the q-analog of the binomial coefficient, defined as
  `qFactorial n q / (qFactorial k q * qFactorial (n - k) q)`.

## Implementation notes

TODO

## Notation

TODO
-/

@[expose] public section

section qNat

/-
The q-analog of a natural number n is the sum 1 + q + ... + q^(n-1).
-/
def qNat {R : Type*} [Semiring R] : ℕ → R → R
  | 0, _     => 0
  | n + 1, q => qNat n q + q ^ n

/- The q-analog of 0 is 0. -/
@[simp]
lemma qNat_zero {R : Type*} [Semiring R] (q : R) :
    qNat 0 q = 0 := rfl

/- The q-analog of 1 is 1. -/
@[simp]
lemma qNat_one {R : Type*} [Semiring R] (q : R) :
    qNat 1 q = 1 := by
  simp [qNat]

/- The q-analog of 2 is 1 + q. -/
@[simp]
lemma qNat_two {R : Type*} [Semiring R] (q : R) :
    qNat 2 q = 1 + q := by
  simp [qNat]

/- The q-analog of n + 1 is the q-analog of n plus q^n. -/
lemma qNat_succ {R : Type*} [Semiring R] (n : ℕ) (q : R) :
    qNat (n + 1) q = qNat n q + q ^ n := rfl

/- The q-analog of n, evaluated at q = 0, is 0 if n = 0 and 1 otherwise -/
@[simp]
lemma qNat_zero' {R : Type*} [Semiring R] (n : ℕ) :
    qNat n (0 : R) = if n = 0 then 0 else 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [qNat, ih, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
    split_ifs with h
    · rw [h, pow_zero]
      exact AddZeroClass.zero_add 1
    · rw [zero_pow h]
      exact AddMonoid.add_zero 1

/- The q-analog of n, evaluated at q = 1, is n -/
@[simp]
lemma qNat_one' {R : Type*} [Semiring R] (n : ℕ) :
    qNat n (1 : R) = (n : R) := by
  induction n with
  | zero => rw [qNat, Nat.cast_zero]
  | succ n ih => rw [qNat, ih, one_pow, Nat.cast_succ, add_comm]

/- The q-analog of n is equal to 1 + q + ... + q^(n-1) -/
theorem qNat_eq_sum_qPow {R : Type*} [Semiring R] (n : ℕ) (q : R) :
    qNat n q = ∑ i ∈ Finset.range n, q ^ i := by
  induction n with
  | zero => simp [qNat]
  | succ n ih =>
    rw [qNat, ih]
    exact Eq.symm (Finset.sum_range_succ (HPow.hPow q) n)

/- The q-analog of n + 1 is 1 + q times the q-analog of n. -/
lemma qNat_succ' {R : Type*} [Semiring R] (n : ℕ) (q : R) :
    qNat (n + 1) q = 1 + q * qNat n q := by
  induction n with
  | zero => simp [qNat]
  | succ n ih =>
    rw [qNat_eq_sum_qPow _ q, qNat_eq_sum_qPow _ q, add_comm 1 _, ← pow_zero q, Finset.mul_sum]
    simp_rw [← pow_succ']
    rw [← Finset.sum_range_succ']

/- The q-analog of n is equal to (1 - q^n) / (1 - q) -/
theorem qNat_eq_geom_sum {R : Type*} [Field R] [Nontrivial R] (n : ℕ) (q : R)
    (hq : q ≠ 1) :
    qNat n q = (1 - q ^ n) / (1 - q) := by
  rw [qNat_eq_sum_qPow, geom_sum_eq hq _]
  grind

/- The q-analog of m + n is the q-analog of m plus q ^ m times the q-analog of n. -/
theorem qNat_add_right {R : Type*} [Semiring R] (m n : ℕ) (q : R) :
    qNat (m + n) q = qNat m q + q ^ m * qNat n q := by
  rw [qNat_eq_sum_qPow, qNat_eq_sum_qPow, qNat_eq_sum_qPow, Finset.mul_sum]
  rw [Finset.sum_range_add (HPow.hPow q) m n]
  simp_rw [← pow_add]

/- The q-analog of m + n is q ^ n times the q-analog of m plus the q-analog of n. -/
theorem qNat_add_left {R : Type*} [Semiring R] (m n : ℕ) (q : R) :
    qNat (m + n) q = q ^ n * qNat m q + qNat n q := by
  rw [add_comm m n, qNat_add_right]
  grind

/- q-analogs commute with powers of q. -/
theorem qNat_mul_qPow_eq_qPow_mul_qNat {R : Type*} [Semiring R] (m n : ℕ) (q : R) :
    qNat m q * q ^ n = q ^ n * qNat m q := by
  rw [qNat_eq_sum_qPow m, Finset.sum_mul, Finset.mul_sum]
  simp_rw [← pow_add, add_comm]

/- The q-analogs commute. -/
lemma qNat_mul_comm {R : Type*} [Semiring R] (m n : ℕ) (q : R) :
    (qNat m q) * (qNat n q) = (qNat n q) * (qNat m q) := by
  induction m generalizing n with
  | zero => simp [qNat]
  | succ m ih =>
    rw [qNat_succ, mul_add, add_mul, ih]
    suffices q ^ m * qNat n q = qNat n q * q ^ m by
      rw [this]
    exact Eq.symm (qNat_mul_qPow_eq_qPow_mul_qNat n m q)

end qNat

section qFactorial

/-
The q-factorial of n, denoted [n]_q!, is the product [1]_q * [2]_q * ... * [n]_q.
-/
def qFactorial {R : Type*} [Semiring R] : ℕ → R → R
  | 0, _     => 1
  | n + 1, q => qFactorial n q * qNat (n + 1) q

/- The q-factorial of 0 is 1. -/
@[simp]
lemma qFactorial_zero {R : Type*} [Semiring R] (q : R) :
    qFactorial 0 q = 1 := rfl

/- The q-factorial of 1 is 1. -/
@[simp]
lemma qFactorial_one {R : Type*} [Semiring R] (q : R) : qFactorial 1 q = 1 := by
  simp [qFactorial, qNat]

/- The q-factorial of n + 1 is the q-factorial of n times the q-analog of n + 1. -/
lemma qFactorial_succ {R : Type*} [Semiring R] (n : ℕ) (q : R) :
    qFactorial (n + 1) q = qFactorial n q * qNat (n + 1) q := rfl

/- The q-factorial of n, evaluated at q = 0, is 1. -/
@[simp]
lemma qFactorial_zero' {R : Type*} [Semiring R] (n : ℕ) : qFactorial n (0 : R) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [qFactorial, ih, qNat_zero', Nat.add_eq_zero_iff, one_ne_zero, and_false,
      ↓reduceIte]
    exact MulOneClass.one_mul 1

/- The q-factorial of n, evaluated at q = 1, is n! -/
@[simp]
lemma qFactorial_one' {R : Type*} [Semiring R] (n : ℕ) :
    qFactorial n (1 : R) = Nat.factorial n := by
  induction n with
  | zero =>
    simp [qFactorial, Nat.factorial_zero]
  | succ n ih =>
    simp [qFactorial, ih, Nat.factorial_succ, mul_comm]

/- q-factorials commute with powers of q. -/
theorem qFactorial_mul_qPow_eq_qPow_mul_qFactorial {R : Type*} [Semiring R] (n : ℕ) (m : ℕ)
    (q : R) :
    qFactorial n q * q ^ m = q ^ m * qFactorial n q := by
  induction n with
  | zero => simp [qFactorial]
  | succ n ih =>
    rw [qFactorial_succ, mul_assoc, qNat_mul_qPow_eq_qPow_mul_qNat, ← mul_assoc, ih, ← mul_assoc]

/- q-analogs commute with q-factorials. -/
theorem qFactorial_mul_qNat_eq_qNat_mul_qFactorial {R : Type*} [Semiring R] (m n : ℕ) (q : R) :
    qFactorial m q * qNat n q = qNat n q * qFactorial m q := by
  induction m generalizing n with
  | zero => simp [qFactorial]
  | succ m ih =>
    rw [qFactorial_succ, ← mul_assoc, ← ih n, mul_assoc, qNat_mul_comm, mul_assoc]

/- q-factorials commute. -/
theorem qFactorial_mul_comm {R : Type*} [Semiring R] (m n : ℕ) (q : R) :
    (qFactorial m q) * (qFactorial n q) = (qFactorial n q) * (qFactorial m q) := by
  induction m generalizing n with
  | zero => simp [qFactorial]
  | succ m ih =>
    rw [qFactorial_succ, ← mul_assoc, ← ih, mul_assoc, ← qFactorial_mul_qNat_eq_qNat_mul_qFactorial,
      mul_assoc]

end qFactorial

section qBinomial

/-
The q-binomial coefficient, denoted [n choose k]_q, is defined as [n]_q! / ([k]_q! * [n-k]_q!).
-/
def qBinomial {R : Type*} [Semiring R] : ℕ → ℕ → R → R
  | _, 0, _     => 1
  | 0, _, _     => 0
  | n + 1, k + 1, q => qBinomial n k q + q ^ (k + 1) * qBinomial n (k + 1) q

/- The q-binomial coefficient n choose 0 is 1. -/
@[simp]
theorem qBinomial_zero_right {R : Type*} [Semiring R] (n : ℕ) (q : R) : qBinomial n 0 q = 1 := by
  simp [qBinomial]

/- The q-binomial coefficient 0 choose k is 0 for k > 0. -/
@[simp]
theorem qBinomial_zero_succ {R : Type*} [Semiring R] (k : ℕ) (q : R) :
    qBinomial 0 (k + 1) q = 0 := by
  simp [qBinomial]

/- The q-binomial coefficient satisfies the q-Pascal's identity. -/
theorem qBinomial_succ_succ {R : Type*} [Semiring R] (n k : ℕ) (q : R) :
    qBinomial n.succ k.succ q = qBinomial n k q + q ^ k.succ * qBinomial n k.succ q :=
  rfl

/- The q-binomial coefficient satisfies the first q-Pascal's identity. -/
theorem qBinomial_succ_succ' {R : Type*} [Semiring R] (n k : ℕ) (q : R) :
    qBinomial (n + 1) (k + 1) q = qBinomial n k q + q ^ (k + 1) * qBinomial n (k + 1) q :=
  rfl

@[simp]
lemma qBinomial_eq_zero_of_lt {R : Type*} [Semiring R] : ∀ {n k : ℕ} (q : R),
    n < k → qBinomial n k q = 0
  | _, 0, _, hk => absurd hk (Nat.not_lt_zero _)
  | 0, _ + 1, q, _ => qBinomial_zero_succ _ q
  | n + 1, k + 1, q, hk => by
    have hnk : n < k := Nat.lt_of_succ_lt_succ hk
    have hnk1 : n < k + 1 := Nat.lt_of_succ_lt hk
    rw [qBinomial_succ_succ, qBinomial_eq_zero_of_lt q hnk, qBinomial_eq_zero_of_lt q hnk1,
      mul_zero, zero_add 0]

@[simp]
lemma qBinomial_zero {R : Type*} [Semiring R] (k : ℕ) (q : R) :
    qBinomial 0 k q = if k = 0 then 1 else 0 := by
  cases k with
  | zero => simp [qBinomial]
  | succ k => simp [qBinomial]

@[simp]
lemma qBinomial_self {R : Type*} [Semiring R] (n : ℕ) (q : R) : qBinomial n n q = 1 := by
  induction n <;> simp [*, qBinomial]

@[simp]
lemma qBinomial_one {R : Type*} [Semiring R] (n : ℕ) (q : R) :
    qBinomial n 1 q = qNat n q := by
  induction n <;> simp only [qBinomial, qBinomial_zero_right, zero_add, pow_one, qNat, *]
  rw [← qNat_succ, ← qNat_succ']

/- q-factorials commute with powers of q. -/
theorem qBinomial_mul_qPow_eq_qPow_mul_qBinomial {R : Type*} [Semiring R] (n k : ℕ) (m : ℕ)
    (q : R) :
    qBinomial n k q * q ^ m = q ^ m * qBinomial n k q := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    cases k with
    | zero => simp [qBinomial]
    | succ k =>
      rw [qBinomial_succ_succ', add_mul, ih k, mul_assoc, ih (k + 1), ← mul_assoc,
        pow_mul_comm q (k + 1) m, mul_assoc, ← mul_add]


/- The q-binomial coefficient satisfies the second q-Pascal's identity. -/
theorem qBinomial_succ_succ'' {R : Type*} [Semiring R] (n k : ℕ) (q : R) :
    qBinomial (n + 1) (k + 1) q = q ^ (n - k) * qBinomial n k q + qBinomial n (k + 1) q := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp [qBinomial]
    | succ k => simp [qBinomial]
  | succ n ih =>
    cases k with
    | zero =>
      simp [qNat_succ, add_comm (q ^ (n + 1))]
    | succ k =>
      rcases lt_trichotomy k n with hkn | hkn | hkn
      · calc
          qBinomial (n + 1 + 1) (k + 1 + 1) q
              = qBinomial (n + 1) (k + 1) q
                + q ^ (k + 1 + 1) * qBinomial (n + 1) (k + 1 + 1) q := by
            rw [qBinomial_succ_succ']
          _ = q ^ (n - k) * qBinomial n k q + qBinomial n (k + 1) q + q ^ (k + 1 + 1) *
              (q ^ (n - (k + 1)) * qBinomial n (k + 1) q + qBinomial n (k + 1 + 1) q) := by
            nth_rw 1 [ih k, ih (k + 1)]
          _ = q ^ (n - k) * (qBinomial n k q + q ^ (k + 1) * qBinomial n (k + 1) q) +
              (qBinomial n (k + 1) q + q ^ (k + 1 + 1) * qBinomial n (k + 1 + 1) q) := by
            rw [mul_add, mul_add, ← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add]
            rw [(by omega : k + 1 + 1 + (n - (k + 1)) = n + 1)]
            rw [(by omega : n - k + (k + 1) = n + 1)]
            grind
          _ = q ^ (n - k) * qBinomial (n + 1) (k + 1) q + qBinomial (n + 1) (k + 1 + 1) q := by
            rw [add_comm, ← qBinomial_succ_succ', ← qBinomial_succ_succ', add_comm]
          _ = q ^ (n + 1 - (k + 1)) * qBinomial (n + 1) (k + 1) q
              + qBinomial (n + 1) (k + 1 + 1) q := by
            simp
      · simp [hkn]
      · grind [qBinomial_eq_zero_of_lt]

/- The q-binomial coefficient is symmetric in k and n-k. -/
theorem qBinomial_symm {R : Type*} [Semiring R] {n k : ℕ} (h : k ≤ n) (q : R) :
    qBinomial n k q = qBinomial n (n - k) q := by
  induction n generalizing k with
  | zero =>
    rw [nonpos_iff_eq_zero] at h
    simp [h]
  | succ n ih =>
    cases k with
    | zero =>
      simp [qBinomial]
    | succ k =>
      by_cases hkn : k < n
      · rw [qBinomial_succ_succ', ih (by linarith : k ≤ n), ih (by linarith : k + 1 ≤ n), add_comm]
        nth_rw 1 [(by omega : k + 1 = n - (n - (k + 1))), (by omega : n - k = (n - (k + 1) + 1))]
        rw [← qBinomial_succ_succ'' n (n - (k + 1)) q]
        congr; omega
      · rw [(by omega : k = n), qBinomial_self, tsub_self, qBinomial_zero_right]

/- The q-binomial coefficient (n+1) choose k, for k > 0. -/
theorem qBinomial_succ_left {R : Type*} [Semiring R] (n k : ℕ) (q : R) (hk : 0 < k) :
    qBinomial (n + 1) k q = qBinomial n (k - 1) q + q ^ k * qBinomial n k q := by
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := Nat.exists_eq_add_of_le' hk
  rfl

/- The q-binomial coefficient n choose (k+1). -/
theorem qBinomial_succ_right {R : Type*} [Semiring R] (n k : ℕ) (q : R) (hn : 0 < n) :
    qBinomial n (k + 1) q = qBinomial (n - 1) k q + q ^ (k + 1) * qBinomial (n - 1) (k + 1) q := by
  obtain ⟨l, rfl⟩ : ∃ l, n = l + 1 := Nat.exists_eq_add_of_le' hn
  rfl

/- The q-binomial coefficient n choose k can be expressed as a sum. -/
theorem qBinomial_eq_pred_add {R : Type*} [Semiring R] {n k : ℕ} (q : R) (hn : 0 < n) (hk : 0 < k) :
    qBinomial n k q = qBinomial (n - 1) (k - 1) q + q ^ k * qBinomial (n - 1) k q := by
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := Nat.exists_eq_add_of_le' hk
  rw [qBinomial_succ_right _ _ _ hn, Nat.add_one_sub_one]

@[simp]
theorem qBinomial_succ_self {R : Type*} [Semiring R] (n : ℕ) (q : R) : qBinomial n n.succ q = 0 :=
  qBinomial_eq_zero_of_lt q (Nat.lt_succ_self n)

theorem le_of_qBinomial_ne_zero {R : Type*} [Semiring R] {n k : ℕ} (q : R) :
    qBinomial n k q ≠ 0 → k ≤ n := by
  contrapose!
  exact qBinomial_eq_zero_of_lt q

theorem add_one_mul_qBinomial_eq {R : Type*} [CommSemiring R] (q : R) : ∀ n k, qNat (n + 1) q *
    (qBinomial n k q) = qBinomial (n + 1) (k + 1) q * qNat (k + 1) q --:= by sorry
  | 0, 0 => by simp
  | 0, k + 1 => by simp [qNat, qBinomial]
  | n + 1, 0 => by
    simp only [qNat, qBinomial, mul_one, zero_add, pow_one, qBinomial_zero_right,
      qBinomial_one, pow_zero]
    repeat rw [← qNat_succ, ← qNat_succ']
  | n + 1, k + 1 => by
    by_cases hkn : k ≤ n
    · rw [qBinomial_succ_succ'' (n + 1) (k + 1), add_mul _ _ (qNat (k + 1 + 1) q), mul_assoc,
      ← add_one_mul_qBinomial_eq q n (k + 1), qNat_succ (k + 1) _, mul_add,
      ← add_one_mul_qBinomial_eq q n, mul_add (q ^ (n + 1 - (k + 1))) _,
      add_right_comm _ _ (_ * _), ← mul_assoc (q ^ ((n + 1) - (k + 1))) _ _,
      mul_comm (q ^ ((n + 1) - (k + 1))) _, mul_assoc _ (q ^ ((n + 1) - (k + 1))) _,
      ← mul_add, Nat.add_sub_add_right n 1 k, ← qBinomial_succ_succ'', qNat_succ (n + 1) _,
      mul_comm _ (q ^ (k + 1)), ← mul_assoc, ← pow_add, (by omega : (n - k + (k + 1)) = n + 1),
      add_mul]
    · rw [qBinomial_eq_zero_of_lt q (by omega), mul_zero, qBinomial_eq_zero_of_lt q (by omega),
        zero_mul]

theorem qBinomial_mul_qFactorial_mul_qFactorial {R : Type*} [Semiring R] {n k : ℕ} (h : k ≤ n)
   (q : R) : qBinomial n k q * qFactorial k q * qFactorial (n - k) q = qFactorial n q := by
  induction n generalizing k with
  | zero =>
    rw [nonpos_iff_eq_zero] at h
    simp [h, qFactorial]
  | succ n ih =>
    cases k with
    | zero =>
      simp [qBinomial, qFactorial]
    | succ k =>
      by_cases hnk : k = n
      · rw [hnk]
        simp
      · rw [qBinomial_succ_succ]
        simp only [Nat.succ_eq_add_one, Nat.reduceSubDiff]
        rw [add_mul, add_mul]
        nth_rw 1 [qFactorial_succ]
        rw [mul_assoc, mul_assoc, ← qFactorial_mul_qNat_eq_qNat_mul_qFactorial _ (k + 1),
            ← mul_assoc, ← mul_assoc, ih (by linarith : k ≤ n),
            (by omega : n - k = (n - k - 1) + 1), qFactorial_succ (n - k - 1), ← mul_assoc,
            mul_assoc (q ^ (k + 1)), mul_assoc (q ^ (k + 1)),
            (by omega : n - k - 1 = n - (k + 1)), ih (by omega : k + 1 ≤ n),
            ← qFactorial_mul_qPow_eq_qPow_mul_qFactorial _ (k + 1), mul_assoc, ← mul_add,
            ← qNat_add_right, qFactorial_succ, (by omega : k + 1 + (n - (k + 1) + 1) = n + 1)]

theorem qBinomial_mul {R : Type*} [Semiring R] {n k s : ℕ} (hsk : s ≤ k) (hkn : k ≤ n) (q : R) :
    qBinomial n k q * qBinomial k s q = qBinomial n s q * qBinomial (n - s) (k - s) q := by
  induction n generalizing k s with
  | zero =>
    simp only [qBinomial_zero, ite_mul, one_mul, zero_mul, zero_tsub, mul_ite, mul_one, mul_zero]
    by_cases hk : k = 0
    · simp [hk]
    · grind
  | succ n ih =>
    cases k with
    | zero =>
      simp [qBinomial, Nat.le_zero.mp hsk]
    | succ k =>
      cases s with
      | zero =>
        simp [qBinomial, mul_one]
      | succ s =>
        by_cases hkn' : k = n
        · simp [hkn']
        · by_cases hsk' : s = k
          · simp [hsk']
          · rw [qBinomial_succ_succ', add_mul, mul_assoc, ih (by linarith) (by omega),
              qBinomial_succ_succ', mul_add, ih (by linarith) (by linarith), ← mul_assoc,
              qBinomial_mul_qPow_eq_qPow_mul_qBinomial, mul_assoc, ih (by omega) (by linarith),
              (by rw [← pow_add]; grind : q ^ (k + 1) = q ^ (s + 1) * q ^ (k - s)), mul_assoc,
              (by omega : n + 1 - (s + 1) = n - s), (by omega : k + 1 - (s + 1) = k - s),
              qBinomial_succ_succ', add_mul, add_assoc, ← mul_add (q ^ (s + 1)), mul_assoc,
              ← mul_assoc, ← qBinomial_mul_qPow_eq_qPow_mul_qBinomial, mul_assoc, ← mul_add,
              (by omega : n - s = (n - s - 1) + 1), (by omega : k - s = (k - s - 1) + 1),
              qBinomial_succ_succ']
            grind

/- # Questa è la roba in Mathlib sui binomiali normali, di cui va scritto un enunciato q-analogo,
# se ha senso. -/

-- theorem choose_eq_factorial_div_factorial {n k : ℕ} (hk : k ≤ n) :
--     choose n k = n ! / (k ! * (n - k)!) := by
--   rw [← choose_mul_factorial_mul_factorial hk, Nat.mul_assoc]
--   exact (mul_div_left _ (Nat.mul_pos (factorial_pos _) (factorial_pos _))).symm

-- theorem add_choose (i j : ℕ) : (i + j).choose j = (i + j)! / (i ! * j !) := by
--   rw [choose_eq_factorial_div_factorial (Nat.le_add_left j i), Nat.add_sub_cancel_right,
--     Nat.mul_comm]

-- theorem add_choose_mul_factorial_mul_factorial (i j : ℕ) :
--     (i + j).choose j * i ! * j ! = (i + j)! := by
--   rw [← choose_mul_factorial_mul_factorial (Nat.le_add_left _ _), Nat.add_sub_cancel_right,
--     Nat.mul_right_comm]

-- theorem factorial_mul_factorial_dvd_factorial {n k : ℕ} (hk : k ≤ n) : k ! * (n - k)! ∣ n ! := by
--   rw [← choose_mul_factorial_mul_factorial hk, Nat.mul_assoc]; exact Nat.dvd_mul_left _ _

-- theorem factorial_mul_factorial_dvd_factorial_add (i j : ℕ) : i ! * j ! ∣ (i + j)! := by
--   suffices i ! * (i + j - i)! ∣ (i + j)! by
--     rwa [Nat.add_sub_cancel_left i j] at this
--   exact factorial_mul_factorial_dvd_factorial (Nat.le_add_right _ _)

-- @[simp]
-- theorem choose_symm {n k : ℕ} (hk : k ≤ n) : choose n (n - k) = choose n k := by
--   rw [choose_eq_factorial_div_factorial hk, choose_eq_factorial_div_factorial (Nat.sub_le _ _),
--     Nat.sub_sub_self hk, Nat.mul_comm]

-- theorem choose_symm_of_eq_add {n a b : ℕ} (h : n = a + b) : Nat.choose n a = Nat.choose n b := by
--   suffices choose n (n - b) = choose n b by
--     rw [h, Nat.add_sub_cancel_right] at this; rwa [h]
--   exact choose_symm (h ▸ le_add_left _ _)

-- theorem choose_symm_add {a b : ℕ} : choose (a + b) a = choose (a + b) b :=
--   choose_symm_of_eq_add rfl

-- theorem choose_symm_half (m : ℕ) : choose (2 * m + 1) (m + 1) = choose (2 * m + 1) m := by
--   apply choose_symm_of_eq_add
--   rw [Nat.add_comm m 1, Nat.add_assoc 1 m m, Nat.add_comm (2 * m) 1, Nat.two_mul m]

-- theorem choose_succ_right_eq (n k : ℕ) : choose n (k + 1) * (k + 1) = choose n k * (n - k) := by
--   have e : (n + 1) * choose n k = choose n (k + 1) * (k + 1) + choose n k * (k + 1) := by
--     rw [← Nat.add_mul, Nat.add_comm (choose _ _), ← choose_succ_succ, add_one_mul_choose_eq]
--   rw [← Nat.sub_eq_of_eq_add e, Nat.mul_comm, ← Nat.mul_sub_left_distrib, Nat.add_sub_add_right]

-- @[simp]
-- theorem choose_succ_self_right : ∀ n : ℕ, (n + 1).choose n = n + 1
--   | 0 => rfl
--   | n + 1 => by rw [choose_succ_succ, choose_succ_self_right n, choose_self]

-- theorem choose_mul_succ_eq (n k : ℕ) : n.choose k * (n + 1) = (n + 1).choose k * (n + 1 - k) := by
--   cases k with
--   | zero => simp
--   | succ k =>
--     obtain hk | hk := le_or_gt (k + 1) (n + 1)
--     · rw [choose_succ_succ, Nat.add_mul, succ_sub_succ, ← choose_succ_right_eq, ← succ_sub_succ,
--         Nat.mul_sub_left_distrib, Nat.add_sub_cancel' (Nat.mul_le_mul_left _ hk)]
--     · rw [choose_eq_zero_of_lt hk, choose_eq_zero_of_lt (n.lt_succ_self.trans hk), Nat.zero_mul,
--         Nat.zero_mul]


--section qPochhammer
