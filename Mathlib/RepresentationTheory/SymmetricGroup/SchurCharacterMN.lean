/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.RepresentationTheory.SymmetricGroup.SchurCharacter
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Basis.Truncate
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.MurnaghanNakayamaRibbon
public import Mathlib.Combinatorics.Enumerative.Partition.Ribbon

/-!
# The Murnaghan-Nakayama rule for the characters of the symmetric group

The Frobenius character formula `p_{cycleType σ} = ∑_μ χ^μ(σ) s_μ` of
`Mathlib/RepresentationTheory/SymmetricGroup/SchurCharacter.lean` turns the
Murnaghan-Nakayama rule for symmetric polynomials, `p_r · s_μ = ∑ (-1)^height s_ν` (the sum being
over the shapes `ν` obtained from `μ` by adding a ribbon of `r` boxes), into a recursion for the
values of the Schur class functions: removing a part `r` from the cycle type expresses `χ^ν` as the
signed sum of the `χ^μ` over the shapes `μ` obtained from `ν` by removing a ribbon of `r` boxes.

As a consequence the Schur class functions take integer values.

## Main results

* `Equiv.Perm.pProd_cycleTypeList_eq_sum_of_le` : the Frobenius character formula in any number
  `k ≥ n` of variables.
* `Equiv.Perm.schurChar_mnRule` : **the Murnaghan-Nakayama rule for characters**, with the
  ribbons described as in
  `Mathlib/RingTheory/MvPolynomial/Symmetric/Schur/MurnaghanNakayama.lean`.
* `Equiv.Perm.schurChar_mnRule_ribbon` : the same rule, with the sum indexed by the shapes `μ`
  such that `ν / μ` is a ribbon and the sign given by the number of its rows.
* `Equiv.Perm.schurChar_of_cycleTypeList_eq_singleton` : the value at an `n`-cycle is zero
  unless the shape is a hook.
* `Equiv.Perm.exists_intCast_schurChar` : the values of the Schur class functions are integers.
-/

@[expose] public section

open Young

open Equiv MvPolynomial Finset List

namespace Equiv.Perm


variable {n k N r : ℕ}

/-! ### The Frobenius character formula in any number of variables -/

/-- Two symmetric homogeneous polynomials of degree `n` in `M ≥ m ≥ n` variables which have
the same truncation to `m` variables are equal. -/
lemma eq_of_truncVars_eq {m M : ℕ} (hn : n ≤ m) (h : m ≤ M) {p q : MvPolynomial (Fin M) ℚ}
    (hp : p ∈ symHomogeneousSubmodule M n ℚ) (hq : q ∈ symHomogeneousSubmodule M n ℚ)
    (heq : truncVars m M ℚ p = truncVars m M ℚ q) : p = q := by
  have hsub : truncSub h n ℚ (⟨p, hp⟩ : symHomogeneousSubmodule M n ℚ)
      = truncSub h n ℚ (⟨q, hq⟩ : symHomogeneousSubmodule M n ℚ) := Subtype.ext heq
  exact congrArg Subtype.val ((truncEquiv hn h ℚ).injective hsub)

/-- **The Frobenius character formula** in `k ≥ n` variables: the power sum attached to the
cycle type of `σ ∈ S_n` expands over the Schur polynomials in `k` variables with the values
of the Schur class functions at `σ` as coefficients. -/
theorem pProd_cycleTypeList_eq_sum_of_le (hnk : n ≤ k) (σ : Perm (Fin n)) :
    pProd k ℚ (cycleTypeList σ)
      = ∑ μ : Nat.Partition n, schurChar μ σ • schurPoly (Fin k) ℚ μ.partsList := by
  refine eq_of_truncVars_eq (le_refl n) hnk
    (pProd_mem_symHomogeneousSubmodule (cycleTypePart hnk σ))
    (Submodule.sum_mem _ fun μ _ => Submodule.smul_mem _ _
      (schurPoly_mem_symHomogeneousSubmodule (natPartitionEquivPartLengthLe hnk μ))) ?_
  rw [truncVars_pProd hnk (isPart_cycleTypeList σ), map_sum,
    pProd_cycleTypeList_eq_sum σ]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_smul, truncVars_schurPoly hnk (Nat.Partition.isPart_partsList μ)
    (le_of_eq (Nat.Partition.sum_partsList μ))]

/-! ### The Murnaghan-Nakayama rule -/

/-- Adding a ribbon of `r` boxes to a partition of `n` gives a partition of `N = n + r`
with at most `N` parts. -/
lemma mnShapeIdx_aux (hr : 0 < r) (hN : n + r = N) (μ : Nat.Partition n) {k : ℕ} (hk : k < N)
    (hadd : MNAddable μ.partsList r k) :
    IsPart (mnShape μ.partsList r k) ∧ (mnShape μ.partsList r k).sum = N ∧
      (mnShape μ.partsList r k).length ≤ N := by
  refine ⟨isPart_mnShape (Nat.Partition.isPart_partsList μ) hr hadd, ?_, ?_⟩
  · rw [sum_mnShape (Nat.Partition.isPart_partsList μ) hr, Nat.Partition.sum_partsList, hN]
  · exact (length_mnShape_le _ _ _).trans
      (max_le hk ((Nat.Partition.length_partsList_le μ).trans (by omega)))

/-- Regrouping the shapes obtained by adding a ribbon: only the shape `mnShape μ r k`
contributes to the sum over the partitions of `N`. -/
lemma sum_ite_mnShape_smul (hr : 0 < r) (hN : n + r = N) (μ : Nat.Partition n) {k : ℕ}
    (hk : k < N) (a : ℚ) :
    ∑ ν : Nat.Partition N,
        (if MNAddable μ.partsList r k ∧ mnShape μ.partsList r k = ν.partsList then a else 0)
          • schurPoly (Fin N) ℚ ν.partsList
      = if MNAddable μ.partsList r k then
          a • schurPoly (Fin N) ℚ (mnShape μ.partsList r k) else 0 := by
  classical
  by_cases hadd : MNAddable μ.partsList r k
  · rw [ite_eq_left hadd]
    set ν0 : Nat.Partition N :=
      Nat.Partition.ofList (mnShape μ.partsList r k) (mnShapeIdx_aux hr hN μ hk hadd).1
        (mnShapeIdx_aux hr hN μ hk hadd).2.1 with hν0
    have hν0l : ν0.partsList = mnShape μ.partsList r k := by rw [hν0]; simp
    have h0 : ∀ ν ∈ (Finset.univ : Finset (Nat.Partition N)), ν ≠ ν0 →
        (if MNAddable μ.partsList r k ∧ mnShape μ.partsList r k = ν.partsList then a else 0)
          • schurPoly (Fin N) ℚ ν.partsList = 0 := by
      intro ν _ hne
      rw [ite_eq_right (fun hcond => hne (Nat.Partition.partsList_injective
        (by rw [hν0l]; exact hcond.2.symm))), zero_smul]
    rw [Finset.sum_eq_single_of_mem ν0 (Finset.mem_univ _) h0, hν0l,
      ite_eq_left ⟨hadd, rfl⟩]
  · rw [ite_eq_right hadd]
    refine Finset.sum_eq_zero fun ν _ => ?_
    rw [ite_eq_right (fun hc => hadd hc.1), zero_smul]

/-- **The Murnaghan-Nakayama rule for the characters of the symmetric group**: if the cycle
type of `σ ∈ S_N` is obtained from the one of `τ ∈ S_n` by adding a part `r`, then the value
`χ^ν(σ)` is the signed sum of the values `χ^μ(τ)` over the shapes `μ` from which `ν` is
obtained by adding a ribbon of `r` boxes, the sign being `(-1)` to the height of the
ribbon. -/
theorem schurChar_mnRule (hr : 0 < r) (hN : n + r = N)
    (τ : Perm (Fin n)) (σ : Perm (Fin N))
    (hperm : (cycleTypeList σ).Perm (r :: cycleTypeList τ)) (ν : Nat.Partition N) :
    schurChar ν σ
      = ∑ μ : Nat.Partition n, ∑ k : Fin N,
          if MNAddable μ.partsList r (k : ℕ) ∧ mnShape μ.partsList r (k : ℕ) = ν.partsList then
            ((-1 : ℚ) ^ mnHeight μ.partsList r (k : ℕ)) * schurChar μ τ else 0 := by
  classical
  have hle : n ≤ N := by omega
  set c : Nat.Partition N → ℚ := fun ρ => ∑ μ : Nat.Partition n, ∑ k : Fin N,
      if MNAddable μ.partsList r (k : ℕ) ∧ mnShape μ.partsList r (k : ℕ) = ρ.partsList then
        ((-1 : ℚ) ^ mnHeight μ.partsList r (k : ℕ)) * schurChar μ τ else 0 with hc
  have key : ∑ ρ : Nat.Partition N, schurChar ρ σ • schurPoly (Fin N) ℚ ρ.partsList
      = ∑ ρ : Nat.Partition N, c ρ • schurPoly (Fin N) ℚ ρ.partsList := by
    rw [← pProd_cycleTypeList_eq_sum σ, pProd_of_perm N ℚ hperm, pProd_cons,
      pProd_cycleTypeList_eq_sum_of_le hle τ, Finset.mul_sum]
    have hrhs : ∑ ρ : Nat.Partition N, c ρ • schurPoly (Fin N) ℚ ρ.partsList
        = ∑ μ : Nat.Partition n, ∑ k : Fin N,
            if MNAddable μ.partsList r (k : ℕ) then
              (((-1 : ℚ) ^ mnHeight μ.partsList r (k : ℕ)) * schurChar μ τ)
                • schurPoly (Fin N) ℚ (mnShape μ.partsList r (k : ℕ))
            else 0 := by
      rw [hc]
      simp only [Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => sum_ite_mnShape_smul hr hN μ k.isLt _
    rw [hrhs]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [mul_smul_comm, psum_mul_schurPoly (Nat.Partition.isPart_partsList μ)
      ((Nat.Partition.length_partsList_le μ).trans hle) hr, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hadd : MNAddable μ.partsList r (k : ℕ)
    · rw [ite_eq_left hadd, ite_eq_left hadd, smul_comm, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
      push_cast
      ring_nf
    · rw [ite_eq_right hadd, ite_eq_right hadd, smul_zero]
  have hzero : ∑ ρ : PartLengthLe N N,
      (schurChar ((natPartitionEquivPartLengthLe (le_refl N)).symm ρ) σ
        - c ((natPartitionEquivPartLengthLe (le_refl N)).symm ρ))
          • schurPoly (Fin N) ℚ ρ.1 = 0 := by
    rw [← Fintype.sum_equiv (natPartitionEquivPartLengthLe (le_refl N))
      (fun ρ : Nat.Partition N => (schurChar ρ σ - c ρ) • schurPoly (Fin N) ℚ ρ.partsList) _
      (fun ρ => by simp)]
    simp only [sub_smul, Finset.sum_sub_distrib, key, sub_self]
  have hli := linearIndependent_schurPoly N N ℚ
  rw [Fintype.linearIndependent_iff] at hli
  have := hli _ hzero (ν.toPartLengthLe)
  simpa using sub_eq_zero.1 this

/-! ### The rule in the language of ribbons -/

open scoped Classical in
/-- The sum over the rows in which a ribbon can be added reduces to a single term: the
shape `ν` is reached exactly when `ν / μ` is a ribbon, and then only from the row where
the ribbon stops. -/
lemma sum_ite_mnShape_eq_ite_ribbon {μ ν : List ℕ} (hμ : IsPart μ) (hν : IsPart ν)
    (hr : 0 < r) (hsum : ν.sum = μ.sum + r) (hlen : ν.length ≤ N) (a : ℚ) :
    ∑ k : Fin N, (if MNAddable μ r (k : ℕ) ∧ mnShape μ r (k : ℕ) = ν then
        ((-1 : ℚ) ^ mnHeight μ r (k : ℕ)) * a else 0)
      = if ∃ s k, RibbonOn s k μ ν then ((-1 : ℚ) ^ (ribbonHeight μ ν - 1)) * a
        else 0 := by
  classical
  by_cases hex : ∃ s k, RibbonOn s k μ ν
  · obtain ⟨s, k, hrib⟩ := hex
    obtain ⟨-, hadd, hshape⟩ := mnShape_of_ribbonOn hμ hν hrib hr hsum
    have hk : k < N := lt_of_lt_of_le (lt_length_of_ribbonOn hμ hrib) hlen
    rw [ite_eq_left ⟨s, k, hrib⟩]
    have hheight : ribbonHeight μ ν - 1 = mnHeight μ r k := by
      rw [← hshape, ribbonHeight_mnShape hμ hr hadd, Nat.add_sub_cancel]
    rw [Finset.sum_eq_single_of_mem (⟨k, hk⟩ : Fin N) (Finset.mem_univ _) ?_,
      ite_eq_left ⟨hadd, hshape⟩, hheight]
    intro k' _ hne
    refine ite_eq_right fun hcond => hne (Fin.ext ?_)
    have hrib' : RibbonOn (mnPos μ r (k' : ℕ)) (k' : ℕ) μ ν := by
      rw [← hcond.2]
      exact ribbonOn_mnShape hμ hr hcond.1
    exact (RibbonOn.unique hμ hrib' hrib).2
  · rw [ite_eq_right hex]
    refine Finset.sum_eq_zero fun k _ => ite_eq_right fun hcond => hex ?_
    refine ⟨mnPos μ r (k : ℕ), (k : ℕ), ?_⟩
    rw [← hcond.2]
    exact ribbonOn_mnShape hμ hr hcond.1

open scoped Classical in
/-- **The Murnaghan-Nakayama rule for characters, in the language of ribbons**: if the
cycle type of `σ ∈ S_N` is obtained from the one of `τ ∈ S_n` by adding a part `r`, then
`χ^ν(σ)` is the sum of the values `χ^μ(τ)`, over the partitions `μ` of `n` such that the
skew shape `ν / μ` is a ribbon, with the sign `(-1)` to the number of rows of the ribbon
minus one. -/
theorem schurChar_mnRule_ribbon (hr : 0 < r) (hN : n + r = N)
    (τ : Perm (Fin n)) (σ : Perm (Fin N))
    (hperm : (cycleTypeList σ).Perm (r :: cycleTypeList τ)) (ν : Nat.Partition N) :
    schurChar ν σ
      = ∑ μ : Nat.Partition n,
          if μ.IsRibbonOf ν then
            ((-1 : ℚ) ^ (μ.ribbonHeight ν - 1)) * schurChar μ τ else 0 := by
  classical
  rw [schurChar_mnRule hr hN τ σ hperm ν]
  refine Finset.sum_congr rfl fun μ _ => ?_
  exact sum_ite_mnShape_eq_ite_ribbon (Nat.Partition.isPart_partsList μ)
    (Nat.Partition.isPart_partsList ν) hr
    (by rw [Nat.Partition.sum_partsList, Nat.Partition.sum_partsList, hN])
    (Nat.Partition.length_partsList_le ν) _

/-! ### The value at an `n`-cycle -/

/-- **The character of `S_n` at an `n`-cycle** vanishes unless the shape is a *hook*, that
is unless its second row has at most one box, in which case it is `(-1)` to the number of
rows of the shape minus one. -/
theorem schurChar_of_cycleTypeList_eq_singleton (hn : 0 < n) (σ : Perm (Fin n))
    (hsig : cycleTypeList σ = [n]) (ν : Nat.Partition n) :
    schurChar ν σ =
      if ν.youngDiagram.rowLen 1 ≤ 1 then
        (-1 : ℚ) ^ (Multiset.card ν.parts - 1) else 0 := by
  classical
  have hperm : (cycleTypeList σ).Perm (n :: cycleTypeList (1 : Perm (Fin 0))) := by
    rw [hsig, cycleTypeList_one]
    simp
  rw [schurChar_mnRule_ribbon hn (Nat.zero_add n) (1 : Perm (Fin 0)) σ hperm ν]
  set μ0 : Nat.Partition 0 := default with hμ0
  rw [Finset.sum_eq_single_of_mem μ0 (Finset.mem_univ _)
    (fun μ _ hlne => absurd (Subsingleton.elim μ μ0) hlne)]
  have hμ0l : μ0.partsList = [] := by
    refine (Nat.Partition.isPart_partsList μ0).eq_nil_of_sum_eq_zero ?_
    exact Nat.Partition.sum_partsList μ0
  have hchar : schurChar μ0 (1 : Perm (Fin 0)) = 1 := by
    rw [schurChar_one, hμ0l]
    simp [numStdTab_nil]
  rw [hchar, mul_one, Nat.Partition.ribbonHeight_of_isEmpty μ0 ν]
  exact if_congr (Nat.Partition.isRibbonOf_iff_rowLen_one_le μ0 hn.ne') rfl rfl

/-! ### Integrality of the character values -/

/-- The values of the Schur class functions lie in the subring of the integers. -/
lemma schurChar_mem_range_intCast (n : ℕ) (μ : Nat.Partition n) (σ : Perm (Fin n)) :
    schurChar μ σ ∈ (Int.castRingHom ℚ).range := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match hct : cycleTypeList σ with
    | [] =>
      have hn : n = 0 := by
        have hsum := sum_cycleTypeList σ
        rw [hct] at hsum
        simpa using hsum.symm
      subst hn
      rw [Subsingleton.elim σ 1, schurChar_one]
      exact ⟨(numStdTab μ.partsList : ℤ), rfl⟩
    | r :: rest =>
      have hpart : IsPart (r :: rest) := hct ▸ isPart_cycleTypeList σ
      have hr : 0 < r := hpart.pos_of_mem (List.mem_cons_self ..)
      have hsum : r + rest.sum = n := by
        have hsum := sum_cycleTypeList σ
        rw [hct] at hsum
        simpa using hsum
      obtain ⟨τ, hτ⟩ := exists_cycleTypeList_eq (n := rest.sum) hpart.of_cons rfl
      have hlt : rest.sum < n := by omega
      rw [schurChar_mnRule hr (show rest.sum + r = n by omega) τ σ
        (by rw [hct, hτ]) μ]
      refine Subring.sum_mem _ fun ν _ => Subring.sum_mem _ fun k _ => ?_
      split
      · exact Subring.mul_mem _
          (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _)
          (ih rest.sum hlt ν τ)
      · exact Subring.zero_mem _

/-- **The values of the Schur class functions are integers.** -/
theorem exists_intCast_schurChar (μ : Nat.Partition n) (σ : Perm (Fin n)) :
    ∃ z : ℤ, schurChar μ σ = (z : ℚ) := by
  obtain ⟨z, hz⟩ := schurChar_mem_range_intCast n μ σ
  exact ⟨z, hz.symm⟩

end Equiv.Perm
