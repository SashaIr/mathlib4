/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
# Alternants

Following `theories/MPoly/Schur_altdef.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we introduce the alternants

`alt a = ∑_{w ∈ S_m} sign(w) ∏_i x_{w i} ^ (a i)`

attached to an exponent vector `a : Fin m → ℕ`.  This file develops their elementary
properties: they are antisymmetric, they vanish when two exponents agree, and multiplying
by a complete homogeneous symmetric polynomial `h_r` adds all the exponent vectors of
weight `r`.

## Main results

* `MvPolynomial.alt_comp_perm` : `alt (a ∘ v) = sign v • alt a`.
* `MvPolynomial.alt_eq_zero_of_eq` : an alternant with two equal exponents vanishes.
* `MvPolynomial.hsymm_mul_alt` : `h_r * alt a = ∑_{|d| = r} alt (a + d)`.
-/

namespace MvPolynomial

open List MvPolynomial Finset

variable {m : ℕ} {R : Type*} [CommRing R]

/-! ### The monomial expansion of `h_r` -/

lemma sum_count_univ (s : Multiset (Fin m)) : ∑ x, Multiset.count x s = Multiset.card s := by
  classical
  rw [← Multiset.toFinset_sum_count_eq s]
  exact (Finset.sum_subset (Finset.subset_univ _) (by
    intro x _ hx
    simpa using Multiset.count_eq_zero_of_notMem (by simpa using hx))).symm

lemma prod_map_X_toMultiset (d : Fin m →₀ ℕ) :
    ((Finsupp.toMultiset d).map (X (R := R))).prod = monomial d (1 : R) := by
  rw [Finset.prod_multiset_map_count, monomial_eq]
  simp [Finsupp.count_toMultiset, Finsupp.prod]

/-- The complete homogeneous symmetric polynomial `h_r` is the sum of all the monomials of
degree `r`. -/
theorem hsymm_eq_sum_monomial (m r : ℕ) (R : Type*) [CommRing R] :
    hsymm (Fin m) R r
      = ∑ d ∈ Finset.finsuppAntidiag (univ : Finset (Fin m)) r, monomial d (1 : R) := by
  rw [hsymm]
  refine Finset.sum_bij' (i := fun s _ => Multiset.toFinsupp s.1)
    (j := fun d _ => ⟨Finsupp.toMultiset d, by
      have h : d ∈ Finset.finsuppAntidiag (univ : Finset (Fin m)) r := by assumption
      rw [Finset.mem_finsuppAntidiag] at h
      rw [Finsupp.card_toMultiset, ← h.1, Finsupp.sum_fintype]
      · rfl
      · simp⟩) ?_ ?_ ?_ ?_ ?_
  · intro s _
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, by simp⟩
    simp
  · intro d _
    exact Finset.mem_univ _
  · intro s _
    exact Subtype.ext (by simp)
  · intro d _
    simp
  · intro s _
    have := prod_map_X_toMultiset (R := R) (Multiset.toFinsupp s.1)
    rwa [Multiset.toFinsupp_toMultiset] at this

/-! ### Alternants -/

/-- The alternant of an exponent vector `a`:
`alt a = ∑_{w ∈ S_m} sign(w) ∏_i x_{w i} ^ (a i)`. -/
noncomputable def alt (m : ℕ) (R : Type*) [CommRing R] (a : Fin m → ℕ) :
    MvPolynomial (Fin m) R :=
  ∑ w : Equiv.Perm (Fin m), (Equiv.Perm.sign w : ℤ) • ∏ i, X (w i) ^ a i

/-- Permuting the exponents of an alternant multiplies it by the sign of the
permutation. -/
theorem alt_comp_perm (a : Fin m → ℕ) (v : Equiv.Perm (Fin m)) :
    alt m R (a ∘ v) = (Equiv.Perm.sign v : ℤ) • alt m R a := by
  rw [alt, alt, Finset.smul_sum]
  refine Fintype.sum_bijective (fun w => w * v⁻¹) (Group.mulRight_bijective _) _ _ ?_
  intro w
  have hprod : ∏ i, X (R := R) (w i) ^ a (v i) = ∏ j, X (R := R) ((w * v⁻¹) j) ^ a j := by
    rw [← Equiv.prod_comp v (fun j => X (R := R) ((w * v⁻¹) j) ^ a j)]
    simp
  simp only [Function.comp_apply]
  rw [hprod, smul_smul]
  have hsign : Equiv.Perm.sign v * Equiv.Perm.sign (w * v⁻¹) = Equiv.Perm.sign w := by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, mul_comm (Equiv.Perm.sign w),
      ← mul_assoc, Int.units_mul_self, one_mul]
  congr 1
  exact_mod_cast congrArg (fun u : ℤˣ => (u : ℤ)) hsign.symm

/-- An alternant with two equal exponents vanishes. -/
theorem alt_eq_zero_of_eq {a : Fin m → ℕ} {i j : Fin m} (hij : i ≠ j) (h : a i = a j) :
    alt m R a = 0 := by
  have hcomp : ∀ k, a (Equiv.swap i j k) = a k := by
    intro k
    rcases eq_or_ne k i with rfl | hk
    · simp [h]
    rcases eq_or_ne k j with rfl | hk'
    · simp [Equiv.swap_apply_right, h]
    · simp [Equiv.swap_apply_of_ne_of_ne hk hk']
  rw [alt]
  refine Finset.sum_involution (fun w _ => w * Equiv.swap i j) ?_ ?_
    (fun _ _ => Finset.mem_univ _) ?_
  · intro w _
    have hprod : ∏ k, X (R := R) ((w * Equiv.swap i j) k) ^ a k
        = ∏ k, X (R := R) (w k) ^ a k := by
      calc ∏ k, X (R := R) ((w * Equiv.swap i j) k) ^ a k
          = ∏ k, X (R := R) (w (Equiv.swap i j k)) ^ a (Equiv.swap i j k) := by
            refine Finset.prod_congr rfl fun k _ => ?_
            rw [hcomp k]
            rfl
        _ = ∏ k, X (R := R) (w k) ^ a k :=
            Equiv.prod_comp (Equiv.swap i j) (fun k => X (R := R) (w k) ^ a k)
    rw [hprod, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij]
    push_cast
    simp [neg_smul]
  · intro w _ _ hcon
    have h2 := congrArg (fun (u : Equiv.Perm (Fin m)) => u i) hcon
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] at h2
    exact hij (w.injective h2).symm
  · intro w _
    simp [mul_assoc]

/-- Multiplying a single monomial of the alternant by `h_r`. -/
lemma hsymm_mul_prod (r : ℕ) (w : Equiv.Perm (Fin m)) (a : Fin m → ℕ) :
    hsymm (Fin m) R r * ∏ i, X (R := R) (w i) ^ a i
      = ∑ e ∈ Finset.finsuppAntidiag (univ : Finset (Fin m)) r,
          ∏ i, X (R := R) (w i) ^ (a i + e i) := by
  rw [hsymm_eq_sum_monomial, Finset.sum_mul]
  refine Finset.sum_nbij' (i := fun d => Finsupp.equivMapDomain w.symm d)
    (j := fun e => Finsupp.equivMapDomain w e) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    rw [Finset.mem_finsuppAntidiag] at hd ⊢
    refine ⟨?_, by simp⟩
    rw [← hd.1]
    exact Fintype.sum_equiv w _ _ (fun i => by simp)
  · intro e he
    rw [Finset.mem_finsuppAntidiag] at he ⊢
    refine ⟨?_, by simp⟩
    rw [← he.1]
    exact Fintype.sum_equiv w.symm _ _ (fun i => by simp)
  · intro d _
    ext i
    simp
  · intro e _
    ext i
    simp
  · intro d _
    have h1 : (monomial d (1 : R)) = ∏ i, X (R := R) (w i) ^ d (w i) := by
      rw [Equiv.prod_comp w (fun j => X (R := R) j ^ d j), monomial_eq]
      simp [Finsupp.prod, ← Finsupp.prod_pow]
    rw [h1, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← pow_add, Nat.add_comm]
    simp

/-- Multiplying an alternant by the complete homogeneous symmetric polynomial `h_r` adds
all the exponent vectors of weight `r`. -/
theorem hsymm_mul_alt (r : ℕ) (a : Fin m → ℕ) :
    hsymm (Fin m) R r * alt m R a
      = ∑ d ∈ Finset.finsuppAntidiag (univ : Finset (Fin m)) r, alt m R (a + ⇑d) := by
  rw [alt, Finset.mul_sum]
  have hterm : ∀ w : Equiv.Perm (Fin m),
      hsymm (Fin m) R r * ((Equiv.Perm.sign w : ℤ) • ∏ i, X (R := R) (w i) ^ a i)
        = ∑ d ∈ Finset.finsuppAntidiag (univ : Finset (Fin m)) r,
            (Equiv.Perm.sign w : ℤ) • ∏ i, X (R := R) (w i) ^ ((a + ⇑d) i) := by
    intro w
    rw [mul_smul_comm, hsymm_mul_prod, Finset.smul_sum]
    rfl
  simp only [hterm]
  rw [Finset.sum_comm]
  rfl

end MvPolynomial
