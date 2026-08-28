/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.RingTheory.MvPolynomial.Symmetric.Basis.OmegaMul
import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.LittlewoodRichardson

/-!
# Symmetries of the Littlewood–Richardson coefficients

Following `theories/LRrule/freeSchur.v` of [Coq-Combi](https://github.com/math-comp/Coq-Combi), we
deduce from the Littlewood–Richardson rule of
`Mathlib/RingTheory/MvPolynomial/Symmetric/Schur/LittlewoodRichardson.lean` the two
symmetries of the Littlewood–Richardson coefficients: they are symmetric in the two lower indices,
and invariant under conjugating all three partitions (Coq `LRtab_coeff_conj`).

The proofs rewrite the Littlewood–Richardson rule as an expansion in the Schur basis of
the module of symmetric homogeneous polynomials, where the coefficients can be read off,
and use the commutativity of the product for the first symmetry and the multiplicativity
of the involution `omega` for the second.

## Main results

* `MvPolynomial.schurPoly_mul_eq_sum_partIdx` : the Littlewood–Richardson rule, indexed by the
  partitions of `n` with at most `m` parts.
* `MvPolynomial.lrCoeff_comm` : `c^nu_{lam, mu} = c^nu_{mu, lam}`.
* `MvPolynomial.lrCoeff_conjPart` : `c^{nu'}_{lam', mu'} = c^nu_{lam, mu}` (Coq
  `LRtab_coeff_conj`).
-/

namespace MvPolynomial

open List MvPolynomial

variable {m n : ℕ} {R : Type*}

/-! ### The Littlewood–Richardson rule indexed by `PartIdx` -/

/-- A sum over the partitions of `n` (as `Nat.Partition`) is a sum over `PartIdx n m`, as
soon as `n ≤ m`. -/
lemma sum_natPartition_eq_sum_partIdx {M : Type*} [AddCommMonoid M] (hnm : n ≤ m)
    (f : List ℕ → M) : ∑ nu : Nat.Partition n, f nu.partsList = ∑ lam : PartIdx n m, f lam.1 := by
  classical
  rw [← sum_partFinset_eq_sum_partIdx hnm, ← Finset.sum_coe_sort (partFinset n) f]
  refine (Fintype.sum_equiv ((Equiv.subtypeEquivRight fun l => by
    rw [mem_partFinset]).trans (listPartEquivNatPartition n)) _ _ fun p => ?_).symm
  have hp : ((listPartEquivNatPartition n) ((Equiv.subtypeEquivRight
      (fun l => by rw [mem_partFinset] : ∀ l : List ℕ,
        l ∈ partFinset n ↔ IsPart l ∧ l.sum = n)) p)).partsList = (p : List ℕ) := by
    rw [Nat.Partition.partsList, listPartEquivNatPartition_apply]
    exact sortDesc_coe (mem_partFinset.1 p.2).1
  rw [Equiv.trans_apply, hp]

/-- **The Littlewood–Richardson rule**, with the product expanded over the partitions of
`n = |lam| + |mu|` with at most `m` parts. -/
theorem schurPoly_mul_eq_sum_partIdx [CommRing R] {lam mu : List ℕ} (hn : lam.sum + mu.sum = n)
    (hnm : n ≤ m) :
    schurPoly (Fin m) R lam * schurPoly (Fin m) R mu
      = ∑ nu : PartIdx n m, lrCoeff lam mu nu.1 • schurPoly (Fin m) R nu.1 := by
  subst hn
  rw [schurPoly_mul_schurPoly]
  exact sum_natPartition_eq_sum_partIdx hnm
    (fun l => lrCoeff lam mu l • schurPoly (Fin m) R l)

/-- Two expansions of the same symmetric homogeneous polynomial in the Schur family have
the same coefficients. -/
theorem eq_of_sum_nsmul_schurPoly_eq {c d : PartIdx n m → ℕ}
    (h : ∑ nu : PartIdx n m, c nu • schurPoly (Fin m) ℤ nu.1
      = ∑ nu : PartIdx n m, d nu • schurPoly (Fin m) ℤ nu.1) : c = d := by
  have hsub : ∑ nu : PartIdx n m, (c nu : ℤ) • schurBasis m n ℤ nu
      = ∑ nu : PartIdx n m, (d nu : ℤ) • schurBasis m n ℤ nu := by
    refine Subtype.ext ?_
    push_cast
    simpa only [Submodule.coe_sum, SetLike.val_smul, schurBasis_apply, coe_schurSub,
      natCast_zsmul] using h
  funext nu
  have hc := congrArg (fun x => (schurBasis m n ℤ).repr x nu) hsub
  simp only [Module.Basis.repr_sum_self] at hc
  exact_mod_cast hc

/-! ### The two symmetries -/

/-- The Littlewood–Richardson coefficients are symmetric in their two lower indices. -/
theorem lrCoeff_comm {lam mu nu : List ℕ} (hnu : IsPart nu) (hsum : nu.sum = lam.sum + mu.sum) :
    lrCoeff lam mu nu = lrCoeff mu lam nu := by
  set n := lam.sum + mu.sum with hn
  have hmul : ∑ rho : PartIdx n n, lrCoeff lam mu rho.1 • schurPoly (Fin n) ℤ rho.1
      = ∑ rho : PartIdx n n, lrCoeff mu lam rho.1 • schurPoly (Fin n) ℤ rho.1 := by
    rw [← schurPoly_mul_eq_sum_partIdx (R := ℤ) hn.symm le_rfl,
      ← schurPoly_mul_eq_sum_partIdx (R := ℤ) (by omega) le_rfl, mul_comm]
  exact congrFun (eq_of_sum_nsmul_schurPoly_eq (m := n) hmul)
    ⟨nu, hnu, hsum, le_trans hnu.length_le_sum (le_of_eq hsum)⟩

/-- **The Littlewood–Richardson coefficients are invariant under conjugation** of the
three partitions (Coq `LRtab_coeff_conj`). -/
theorem lrCoeff_conjPart {lam mu nu : List ℕ} (hlam : IsPart lam) (hmu : IsPart mu)
    (hnu : IsPart nu) (hsum : nu.sum = lam.sum + mu.sum) :
    lrCoeff (conjPart lam) (conjPart mu) (conjPart nu) = lrCoeff lam mu nu := by
  set n := lam.sum + mu.sum with hn
  have hab : lam.sum + mu.sum = n := rfl
  have hlamlen : lam.length ≤ n := le_trans hlam.length_le_sum (by omega)
  have hmulen : mu.length ≤ n := le_trans hmu.length_le_sum (by omega)
  set lamIdx : PartIdx lam.sum n := ⟨lam, hlam, rfl, hlamlen⟩ with hlamIdx
  set muIdx : PartIdx mu.sum n := ⟨mu, hmu, rfl, hmulen⟩ with hmuIdx
  set F : symHomogeneousSubmodule n n ℤ :=
    mulSub n ℤ hab (schurSub n lam.sum ℤ lamIdx) (schurSub n mu.sum ℤ muIdx) with hF
  have h1 : F = ∑ rho : PartIdx n n, lrCoeff lam mu rho.1 • schurSub n n ℤ rho := by
    refine Subtype.ext ?_
    rw [hF, coe_mulSub, coe_schurSub, coe_schurSub]
    rw [schurPoly_mul_eq_sum_partIdx (R := ℤ) hab le_rfl]
    rw [Submodule.coe_sum]
    exact Finset.sum_congr rfl fun rho _ => by simp
  have h2 : (omegaSym n n ℤ le_rfl F : MvPolynomial (Fin n) ℤ)
      = ∑ rho : PartIdx n n, lrCoeff lam mu rho.1 • schurPoly (Fin n) ℤ (conjPart rho.1) := by
    rw [h1, map_sum, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun rho _ => ?_
    rw [map_nsmul, omegaSym_schurSub]
    simp
  have h3 : (omegaSym n n ℤ le_rfl F : MvPolynomial (Fin n) ℤ)
      = schurPoly (Fin n) ℤ (conjPart lam) * schurPoly (Fin n) ℤ (conjPart mu) := by
    rw [hF, omegaSym_mul hab le_rfl, omegaSym_schurSub, omegaSym_schurSub, coe_schurSub,
      coe_schurSub, conjIdx_val, conjIdx_val]
  have hreindex : ∑ rho : PartIdx n n,
        lrCoeff lam mu rho.1 • schurPoly (Fin n) ℤ (conjPart rho.1)
      = ∑ rho : PartIdx n n,
        lrCoeff lam mu (conjPart rho.1) • schurPoly (Fin n) ℤ rho.1 := by
    refine Fintype.sum_equiv (conjPartIdx (le_refl n)) _ _ fun rho => ?_
    rw [conjPartIdx_apply, conjIdx_val, conjPart_conjPart rho.2.1]
  have hconj : (conjPart lam).sum + (conjPart mu).sum = n := by
    rw [sum_conjPart, sum_conjPart]
  have hkey : ∑ rho : PartIdx n n,
        lrCoeff (conjPart lam) (conjPart mu) rho.1 • schurPoly (Fin n) ℤ rho.1
      = ∑ rho : PartIdx n n,
        lrCoeff lam mu (conjPart rho.1) • schurPoly (Fin n) ℤ rho.1 := by
    rw [← schurPoly_mul_eq_sum_partIdx (R := ℤ) hconj le_rfl, ← hreindex, ← h2, h3]
  have hnulen : (conjPart nu).length ≤ n := by
    rw [length_conjPart hnu]
    exact le_trans (le_trans (headD_le_sum nu) (le_of_eq hsum)) le_rfl
  have hnusum : (conjPart nu).sum = n := by rw [sum_conjPart, hsum]
  have := congrFun (eq_of_sum_nsmul_schurPoly_eq (m := n) hkey)
    ⟨conjPart nu, isPart_conjPart hnu, hnusum, hnulen⟩
  rwa [conjPart_conjPart hnu] at this

end MvPolynomial
