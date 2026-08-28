/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.RingTheory.MvPolynomial.Symmetric.Alternant.Basic

/-!
# Power sums and alternants

Following `theories/MPoly/MurnaghanNakayama.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we compute the product of an
alternant `alt a` by a power sum `p_r`: it adds `r` to one of the exponents, in all
possible ways.  We also provide the elementary rearrangement lemma used to sort the
resulting exponent vector: moving the entry in position `k` to position `j ≤ k` multiplies
the alternant by `(-1) ^ (k - j)`.

## Main definitions and results

* `MvPolynomial.psum_mul_alt` : `p_r * alt a = ∑_k alt (a + r e_k)`.
* `MvPolynomial.moveVec b j k` : the vector `b` with the entry at position `k` moved to position
  `j`, the entries in between being shifted one position to the right.
* `MvPolynomial.alt_moveVec` : `alt b = (-1) ^ (k - j) • alt (moveVec b j k)`.
* `MvPolynomial.sum_moveVec` : moving an entry does not change the sum of the entries.
-/

namespace MvPolynomial

open MvPolynomial Finset

variable {m : ℕ} {R : Type*} [CommRing R]

/-! ### Multiplication of an alternant by a power sum -/

/-- Multiplying an alternant by the power sum `p_r` adds `r` to one of the exponents, in
all possible ways. -/
theorem psum_mul_alt (r : ℕ) (a : Fin m → ℕ) :
    psum (Fin m) R r * alt m R a
      = ∑ k : Fin m, alt m R (Function.update a k (a k + r)) := by
  classical
  have hprod : ∀ (w : Equiv.Perm (Fin m)) (k : Fin m),
      ∏ i, X (R := R) (w i) ^ (Function.update a k (a k + r) i)
        = (∏ i, X (R := R) (w i) ^ a i) * X (w k) ^ r := by
    intro w k
    rw [← Finset.mul_prod_erase univ (fun i => X (R := R) (w i) ^
        (Function.update a k (a k + r) i)) (mem_univ k),
      ← Finset.mul_prod_erase univ (fun i => X (R := R) (w i) ^ a i) (mem_univ k)]
    rw [Function.update_self, pow_add]
    rw [Finset.prod_congr rfl (fun i hi => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi) _ a])]
    ring
  have key : ∀ w : Equiv.Perm (Fin m),
      psum (Fin m) R r * ((Equiv.Perm.sign w : ℤ) • ∏ i, X (R := R) (w i) ^ a i)
        = ∑ k : Fin m, (Equiv.Perm.sign w : ℤ) •
            ∏ i, X (R := R) (w i) ^ (Function.update a k (a k + r) i) := by
    intro w
    simp only [hprod w]
    rw [← Finset.smul_sum, ← Finset.mul_sum, mul_smul_comm]
    congr 1
    rw [psum, mul_comm]
    congr 1
    exact (Equiv.sum_comp w fun j => X (R := R) j ^ r).symm
  rw [alt, Finset.mul_sum]
  simp only [key]
  rw [Finset.sum_comm]
  rfl

/-! ### Moving one entry of an exponent vector -/

/-- The vector `b` with the entry in position `k` moved to position `j`, the entries in
positions `j, …, k - 1` being shifted one position to the right. -/
def moveVec (b : Fin m → ℕ) (j : ℕ) (k : Fin m) : Fin m → ℕ := fun i =>
  if (i : ℕ) = j then b k
  else if j < (i : ℕ) ∧ (i : ℕ) ≤ (k : ℕ) then
    b ⟨(i : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
  else b i

lemma moveVec_apply (b : Fin m → ℕ) (j : ℕ) (k i : Fin m) :
    moveVec b j k i =
      if (i : ℕ) = j then b k
      else if j < (i : ℕ) ∧ (i : ℕ) ≤ (k : ℕ) then
        b ⟨(i : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
      else b i := rfl

lemma moveVec_self (b : Fin m → ℕ) (k : Fin m) : moveVec b (k : ℕ) k = b := by
  funext i
  rw [moveVec_apply]
  by_cases h : (i : ℕ) = (k : ℕ)
  · rw [if_pos h, Fin.ext h]
  · rw [if_neg h, if_neg (by omega)]

/-- Moving the entry in position `k` one step to the left is an adjacent transposition. -/
lemma moveVec_swap (b : Fin m → ℕ) (j : ℕ) (k k' : Fin m)
    (hk' : (k' : ℕ) = (k : ℕ) - 1) (hjk : j < (k : ℕ)) :
    moveVec (b ∘ Equiv.swap k' k) j k' = moveVec b j k := by
  have hne : k' ≠ k := by
    intro h; rw [h] at hk'; omega
  funext i
  rw [moveVec_apply, moveVec_apply]
  by_cases hij : (i : ℕ) = j
  · rw [if_pos hij, if_pos hij]
    simp [Function.comp_apply, Equiv.swap_apply_left]
  rw [if_neg hij, if_neg hij]
  by_cases hmid : j < (i : ℕ) ∧ (i : ℕ) ≤ (k' : ℕ)
  · rw [if_pos hmid, if_pos ⟨hmid.1, by omega⟩]
    have h1 : (⟨(i : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ : Fin m) ≠ k' := by
      intro h
      have := congrArg (fun x : Fin m => (x : ℕ)) h
      simp only at this
      omega
    have h2 : (⟨(i : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ : Fin m) ≠ k := by
      intro h
      have := congrArg (fun x : Fin m => (x : ℕ)) h
      simp only at this
      omega
    simp [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]
  rw [if_neg hmid]
  by_cases hik : (i : ℕ) = (k : ℕ)
  · have hik' : i = k := Fin.ext hik
    subst hik'
    rw [if_pos ⟨hjk, le_rfl⟩]
    have : (⟨(i : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ : Fin m) = k' :=
      Fin.ext (by simp [hk'])
    rw [this]
    simp [Function.comp_apply, Equiv.swap_apply_right]
  · rw [if_neg (by omega)]
    have h1 : i ≠ k' := fun h => by
      have := congrArg (fun x : Fin m => (x : ℕ)) h
      simp only at this
      omega
    have h2 : i ≠ k := fun h => hik (congrArg (fun x : Fin m => (x : ℕ)) h)
    simp [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]

/-- Moving one entry of an exponent vector multiplies the alternant by the sign of the
corresponding cycle. -/
theorem alt_moveVec (b : Fin m → ℕ) (j : ℕ) (k : Fin m) (hjk : j ≤ (k : ℕ)) :
    alt m R b = ((-1 : ℤ) ^ ((k : ℕ) - j)) • alt m R (moveVec b j k) := by
  obtain ⟨d, hd⟩ : ∃ d, (k : ℕ) = j + d := ⟨(k : ℕ) - j, by omega⟩
  induction d generalizing b k with
  | zero =>
    have hkj : (k : ℕ) = j := by omega
    subst hkj
    rw [moveVec_self]
    simp
  | succ d ih =>
    have hkpos : 0 < (k : ℕ) := by omega
    set k' : Fin m := ⟨(k : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩ with hk'def
    have hk' : (k' : ℕ) = (k : ℕ) - 1 := rfl
    have hne : k' ≠ k := by
      intro h
      have := congrArg (fun x : Fin m => (x : ℕ)) h
      simp only [hk'] at this
      omega
    have hswap : alt m R (b ∘ Equiv.swap k' k) = - alt m R b := by
      rw [alt_comp_perm, Equiv.Perm.sign_swap hne]
      simp
    have hrec := ih (b ∘ Equiv.swap k' k) k' (by omega) (by omega)
    rw [moveVec_swap b j k k' hk' (by omega), hswap] at hrec
    have hpow : ((-1 : ℤ) ^ ((k : ℕ) - j)) = -((-1 : ℤ) ^ ((k' : ℕ) - j)) := by
      have : (k : ℕ) - j = ((k' : ℕ) - j) + 1 := by omega
      rw [this, pow_succ]
      ring
    rw [hpow, neg_smul, ← hrec, neg_neg]

/-- Moving one entry of a vector does not change the sum of its entries. -/
theorem sum_moveVec (b : Fin m → ℕ) (j : ℕ) (k : Fin m) (hjk : j ≤ (k : ℕ)) :
    ∑ i, moveVec b j k i = ∑ i, b i := by
  obtain ⟨d, hd⟩ : ∃ d, (k : ℕ) = j + d := ⟨(k : ℕ) - j, by omega⟩
  induction d generalizing b k with
  | zero =>
    have hkj : (k : ℕ) = j := by omega
    subst hkj
    rw [moveVec_self]
  | succ d ih =>
    set k' : Fin m := ⟨(k : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩ with hk'def
    have hk' : (k' : ℕ) = (k : ℕ) - 1 := rfl
    have hrec := ih (b ∘ Equiv.swap k' k) k' (by omega) (by omega)
    rw [moveVec_swap b j k k' hk' (by omega)] at hrec
    rw [hrec]
    exact Equiv.sum_comp (Equiv.swap k' k) b

end MvPolynomial
