/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Basis.OmegaMul
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.LittlewoodRichardson

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

* `MvPolynomial.schurPoly_mul_eq_sum_partLengthLe` : the Littlewood–Richardson rule, indexed by the
  partitions of `n` with at most `m` parts.
* `MvPolynomial.lrCoeff_comm` : `c^ρ_{μ, ν} = c^ρ_{ν, μ}`.
* `MvPolynomial.lrCoeff_conjPart` : `c^{ρ'}_{μ', ν'} = c^ρ_{μ, ν}` (Coq
  `LRtab_coeff_conj`).
-/

@[expose] public section

open Young

namespace MvPolynomial

open List MvPolynomial

variable {m n : ℕ} {R : Type*}

/-! ### The Littlewood–Richardson rule indexed by `PartLengthLe` -/

/-- A sum over the partitions of `n` (as `Nat.Partition`) is a sum over `PartLengthLe n m`, as
soon as `n ≤ m`. -/
lemma sum_natPartition_eq_sum_partLengthLe {M : Type*} [AddCommMonoid M] (hnm : n ≤ m)
    (f : List ℕ → M) : ∑ ν : Nat.Partition n, f ν.partsList = ∑ μ : PartLengthLe n m, f μ.1 := by
  classical
  rw [← sum_partFinset_eq_sum_partLengthLe hnm, ← Finset.sum_coe_sort (partFinset n) f]
  refine (Fintype.sum_equiv ((Equiv.subtypeEquivRight fun l => by
    rw [mem_partFinset]).trans (listPartEquivNatPartition n)) _ _ fun p => ?_).symm
  have hp : ((listPartEquivNatPartition n) ((Equiv.subtypeEquivRight
      (fun l => by rw [mem_partFinset] : ∀ l : List ℕ,
        l ∈ partFinset n ↔ IsPart l ∧ l.sum = n)) p)).partsList = (p : List ℕ) := by
    rw [Nat.Partition.partsList, listPartEquivNatPartition_apply]
    exact sortDesc_coe (mem_partFinset.1 p.2).1
  rw [Equiv.trans_apply, hp]

/-- **The Littlewood–Richardson rule**, with the product expanded over the partitions of
`n = |μ| + |ν|` with at most `m` parts. -/
theorem schurPoly_mul_eq_sum_partLengthLe [CommRing R] {μ ν : List ℕ} (hn : μ.sum + ν.sum = n)
    (hnm : n ≤ m) :
    schurPoly (Fin m) R μ * schurPoly (Fin m) R ν
      = ∑ ρ : PartLengthLe n m, lrCoeff μ ν ρ.1 • schurPoly (Fin m) R ρ.1 := by
  subst hn
  rw [schurPoly_mul_schurPoly]
  exact sum_natPartition_eq_sum_partLengthLe hnm
    (fun l => lrCoeff μ ν l • schurPoly (Fin m) R l)

/-- Two expansions of the same symmetric homogeneous polynomial in the Schur family have
the same coefficients. -/
theorem eq_of_sum_nsmul_schurPoly_eq {c d : PartLengthLe n m → ℕ}
    (h : ∑ ν : PartLengthLe n m, c ν • schurPoly (Fin m) ℤ ν.1
      = ∑ ν : PartLengthLe n m, d ν • schurPoly (Fin m) ℤ ν.1) : c = d := by
  have hsub : ∑ ν : PartLengthLe n m, (c ν : ℤ) • schurBasis m n ℤ ν
      = ∑ ν : PartLengthLe n m, (d ν : ℤ) • schurBasis m n ℤ ν := by
    refine Subtype.ext ?_
    push_cast
    simpa only [Submodule.coe_sum, SetLike.val_smul, schurBasis_apply, coe_schurSub,
      natCast_zsmul] using h
  funext ν
  have hc := congrArg (fun x => (schurBasis m n ℤ).repr x ν) hsub
  simp only [Module.Basis.repr_sum_self] at hc
  exact_mod_cast hc

/-! ### The two symmetries -/

/-- The Littlewood–Richardson coefficients are symmetric in their two lower indices. -/
theorem lrCoeff_comm {μ ν ρ : List ℕ} (hρ : IsPart ρ) (hsum : ρ.sum = μ.sum + ν.sum) :
    lrCoeff μ ν ρ = lrCoeff ν μ ρ := by
  set n := μ.sum + ν.sum with hn
  have hmul : ∑ κ : PartLengthLe n n, lrCoeff μ ν κ.1 • schurPoly (Fin n) ℤ κ.1
      = ∑ κ : PartLengthLe n n, lrCoeff ν μ κ.1 • schurPoly (Fin n) ℤ κ.1 := by
    rw [← schurPoly_mul_eq_sum_partLengthLe (R := ℤ) hn.symm le_rfl,
      ← schurPoly_mul_eq_sum_partLengthLe (R := ℤ) (by omega) le_rfl, mul_comm]
  exact congrFun (eq_of_sum_nsmul_schurPoly_eq (m := n) hmul)
    ⟨ρ, hρ, hsum, le_trans hρ.length_le_sum (le_of_eq hsum)⟩

/-- **The Littlewood–Richardson coefficients are invariant under conjugation** of the
three partitions (Coq `LRtab_coeff_conj`). -/
theorem lrCoeff_conjPart {μ ν ρ : List ℕ} (hμ : IsPart μ) (hν : IsPart ν)
    (hρ : IsPart ρ) (hsum : ρ.sum = μ.sum + ν.sum) :
    lrCoeff (conjPart μ) (conjPart ν) (conjPart ρ) = lrCoeff μ ν ρ := by
  set n := μ.sum + ν.sum with hn
  have hab : μ.sum + ν.sum = n := rfl
  have hμlen : μ.length ≤ n := le_trans hμ.length_le_sum (by omega)
  have hνlen : ν.length ≤ n := le_trans hν.length_le_sum (by omega)
  set μIdx : PartLengthLe μ.sum n := ⟨μ, hμ, rfl, hμlen⟩ with hμIdx
  set νIdx : PartLengthLe ν.sum n := ⟨ν, hν, rfl, hνlen⟩ with hνIdx
  set F : symHomogeneousSubmodule n n ℤ :=
    mulSub n ℤ hab (schurSub n μ.sum ℤ μIdx) (schurSub n ν.sum ℤ νIdx) with hF
  have h1 : F = ∑ κ : PartLengthLe n n, lrCoeff μ ν κ.1 • schurSub n n ℤ κ := by
    refine Subtype.ext ?_
    rw [hF, coe_mulSub, coe_schurSub, coe_schurSub]
    rw [schurPoly_mul_eq_sum_partLengthLe (R := ℤ) hab le_rfl]
    rw [Submodule.coe_sum]
    exact Finset.sum_congr rfl fun κ _ => by simp
  have h2 : (omegaSym n n ℤ le_rfl F : MvPolynomial (Fin n) ℤ)
      = ∑ κ : PartLengthLe n n, lrCoeff μ ν κ.1 • schurPoly (Fin n) ℤ (conjPart κ.1) := by
    rw [h1, map_sum, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [map_nsmul, omegaSym_schurSub]
    simp
  have h3 : (omegaSym n n ℤ le_rfl F : MvPolynomial (Fin n) ℤ)
      = schurPoly (Fin n) ℤ (conjPart μ) * schurPoly (Fin n) ℤ (conjPart ν) := by
    rw [hF, omegaSym_mul hab le_rfl, omegaSym_schurSub, omegaSym_schurSub, coe_schurSub,
      coe_schurSub, PartLengthLe.conj_val, PartLengthLe.conj_val]
  have hreindex : ∑ κ : PartLengthLe n n,
        lrCoeff μ ν κ.1 • schurPoly (Fin n) ℤ (conjPart κ.1)
      = ∑ κ : PartLengthLe n n,
        lrCoeff μ ν (conjPart κ.1) • schurPoly (Fin n) ℤ κ.1 := by
    refine Fintype.sum_equiv (PartLengthLe.conjEquiv (le_refl n)) _ _ fun κ => ?_
    rw [PartLengthLe.conjEquiv_apply, PartLengthLe.conj_val, conjPart_conjPart κ.2.1]
  have hconj : (conjPart μ).sum + (conjPart ν).sum = n := by
    rw [sum_conjPart, sum_conjPart]
  have hkey : ∑ κ : PartLengthLe n n,
        lrCoeff (conjPart μ) (conjPart ν) κ.1 • schurPoly (Fin n) ℤ κ.1
      = ∑ κ : PartLengthLe n n,
        lrCoeff μ ν (conjPart κ.1) • schurPoly (Fin n) ℤ κ.1 := by
    rw [← schurPoly_mul_eq_sum_partLengthLe (R := ℤ) hconj le_rfl, ← hreindex, ← h2, h3]
  have hρlen : (conjPart ρ).length ≤ n := by
    rw [length_conjPart hρ]
    exact le_trans (le_trans (headD_le_sum ρ) (le_of_eq hsum)) le_rfl
  have hρsum : (conjPart ρ).sum = n := by rw [sum_conjPart, hsum]
  have := congrFun (eq_of_sum_nsmul_schurPoly_eq (m := n) hkey)
    ⟨conjPart ρ, isPart_conjPart hρ, hρsum, hρlen⟩
  rwa [conjPart_conjPart hρ] at this

end MvPolynomial
