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

* `MvPolynomial.schurPoly_mul_eq_sum_partIdx` : the Littlewood–Richardson rule, indexed by the
  partitions of `n` with at most `m` parts.
* `MvPolynomial.lrCoeff_comm` : `c^ν_{η, μ} = c^ν_{μ, η}`.
* `MvPolynomial.lrCoeff_conjPart` : `c^{ν'}_{η', μ'} = c^ν_{η, μ}` (Coq
  `LRtab_coeff_conj`).
-/

@[expose] public section

open Young

namespace MvPolynomial

open List MvPolynomial

variable {m n : ℕ} {R : Type*}

/-! ### The Littlewood–Richardson rule indexed by `PartIdx` -/

/-- A sum over the partitions of `n` (as `Nat.Partition`) is a sum over `PartIdx n m`, as
soon as `n ≤ m`. -/
lemma sum_natPartition_eq_sum_partIdx {M : Type*} [AddCommMonoid M] (hnm : n ≤ m)
    (f : List ℕ → M) : ∑ ν : Nat.Partition n, f ν.partsList = ∑ η : PartIdx n m, f η.1 := by
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
`n = |η| + |μ|` with at most `m` parts. -/
theorem schurPoly_mul_eq_sum_partIdx [CommRing R] {η μ : List ℕ} (hn : η.sum + μ.sum = n)
    (hnm : n ≤ m) :
    schurPoly (Fin m) R η * schurPoly (Fin m) R μ
      = ∑ ν : PartIdx n m, lrCoeff η μ ν.1 • schurPoly (Fin m) R ν.1 := by
  subst hn
  rw [schurPoly_mul_schurPoly]
  exact sum_natPartition_eq_sum_partIdx hnm
    (fun l => lrCoeff η μ l • schurPoly (Fin m) R l)

/-- Two expansions of the same symmetric homogeneous polynomial in the Schur family have
the same coefficients. -/
theorem eq_of_sum_nsmul_schurPoly_eq {c d : PartIdx n m → ℕ}
    (h : ∑ ν : PartIdx n m, c ν • schurPoly (Fin m) ℤ ν.1
      = ∑ ν : PartIdx n m, d ν • schurPoly (Fin m) ℤ ν.1) : c = d := by
  have hsub : ∑ ν : PartIdx n m, (c ν : ℤ) • schurBasis m n ℤ ν
      = ∑ ν : PartIdx n m, (d ν : ℤ) • schurBasis m n ℤ ν := by
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
theorem lrCoeff_comm {η μ ν : List ℕ} (hν : IsPart ν) (hsum : ν.sum = η.sum + μ.sum) :
    lrCoeff η μ ν = lrCoeff μ η ν := by
  set n := η.sum + μ.sum with hn
  have hmul : ∑ ρ : PartIdx n n, lrCoeff η μ ρ.1 • schurPoly (Fin n) ℤ ρ.1
      = ∑ ρ : PartIdx n n, lrCoeff μ η ρ.1 • schurPoly (Fin n) ℤ ρ.1 := by
    rw [← schurPoly_mul_eq_sum_partIdx (R := ℤ) hn.symm le_rfl,
      ← schurPoly_mul_eq_sum_partIdx (R := ℤ) (by omega) le_rfl, mul_comm]
  exact congrFun (eq_of_sum_nsmul_schurPoly_eq (m := n) hmul)
    ⟨ν, hν, hsum, le_trans hν.length_le_sum (le_of_eq hsum)⟩

/-- **The Littlewood–Richardson coefficients are invariant under conjugation** of the
three partitions (Coq `LRtab_coeff_conj`). -/
theorem lrCoeff_conjPart {η μ ν : List ℕ} (hη : IsPart η) (hμ : IsPart μ)
    (hν : IsPart ν) (hsum : ν.sum = η.sum + μ.sum) :
    lrCoeff (conjPart η) (conjPart μ) (conjPart ν) = lrCoeff η μ ν := by
  set n := η.sum + μ.sum with hn
  have hab : η.sum + μ.sum = n := rfl
  have hηlen : η.length ≤ n := le_trans hη.length_le_sum (by omega)
  have hμlen : μ.length ≤ n := le_trans hμ.length_le_sum (by omega)
  set ηIdx : PartIdx η.sum n := ⟨η, hη, rfl, hηlen⟩ with hηIdx
  set μIdx : PartIdx μ.sum n := ⟨μ, hμ, rfl, hμlen⟩ with hμIdx
  set F : symHomogeneousSubmodule n n ℤ :=
    mulSub n ℤ hab (schurSub n η.sum ℤ ηIdx) (schurSub n μ.sum ℤ μIdx) with hF
  have h1 : F = ∑ ρ : PartIdx n n, lrCoeff η μ ρ.1 • schurSub n n ℤ ρ := by
    refine Subtype.ext ?_
    rw [hF, coe_mulSub, coe_schurSub, coe_schurSub]
    rw [schurPoly_mul_eq_sum_partIdx (R := ℤ) hab le_rfl]
    rw [Submodule.coe_sum]
    exact Finset.sum_congr rfl fun ρ _ => by simp
  have h2 : (omegaSym n n ℤ le_rfl F : MvPolynomial (Fin n) ℤ)
      = ∑ ρ : PartIdx n n, lrCoeff η μ ρ.1 • schurPoly (Fin n) ℤ (conjPart ρ.1) := by
    rw [h1, map_sum, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [map_nsmul, omegaSym_schurSub]
    simp
  have h3 : (omegaSym n n ℤ le_rfl F : MvPolynomial (Fin n) ℤ)
      = schurPoly (Fin n) ℤ (conjPart η) * schurPoly (Fin n) ℤ (conjPart μ) := by
    rw [hF, omegaSym_mul hab le_rfl, omegaSym_schurSub, omegaSym_schurSub, coe_schurSub,
      coe_schurSub, conjIdx_val, conjIdx_val]
  have hreindex : ∑ ρ : PartIdx n n,
        lrCoeff η μ ρ.1 • schurPoly (Fin n) ℤ (conjPart ρ.1)
      = ∑ ρ : PartIdx n n,
        lrCoeff η μ (conjPart ρ.1) • schurPoly (Fin n) ℤ ρ.1 := by
    refine Fintype.sum_equiv (conjPartIdx (le_refl n)) _ _ fun ρ => ?_
    rw [conjPartIdx_apply, conjIdx_val, conjPart_conjPart ρ.2.1]
  have hconj : (conjPart η).sum + (conjPart μ).sum = n := by
    rw [sum_conjPart, sum_conjPart]
  have hkey : ∑ ρ : PartIdx n n,
        lrCoeff (conjPart η) (conjPart μ) ρ.1 • schurPoly (Fin n) ℤ ρ.1
      = ∑ ρ : PartIdx n n,
        lrCoeff η μ (conjPart ρ.1) • schurPoly (Fin n) ℤ ρ.1 := by
    rw [← schurPoly_mul_eq_sum_partIdx (R := ℤ) hconj le_rfl, ← hreindex, ← h2, h3]
  have hνlen : (conjPart ν).length ≤ n := by
    rw [length_conjPart hν]
    exact le_trans (le_trans (headD_le_sum ν) (le_of_eq hsum)) le_rfl
  have hνsum : (conjPart ν).sum = n := by rw [sum_conjPart, hsum]
  have := congrFun (eq_of_sum_nsmul_schurPoly_eq (m := n) hkey)
    ⟨conjPart ν, isPart_conjPart hν, hνsum, hνlen⟩
  rwa [conjPart_conjPart hν] at this

end MvPolynomial
