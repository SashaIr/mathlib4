/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.RepresentationTheory.SymmetricGroup.SchurCharacter
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Basis.Truncate
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.MurnaghanNakayamaRibbon

/-!
# The Murnaghan-Nakayama rule for the characters of the symmetric group

The Frobenius character formula `p_{cycleType σ} = ∑_λ χ^λ(σ) s_λ` of
`Mathlib/RepresentationTheory/SymmetricGroup/SchurCharacter.lean` turns the
Murnaghan-Nakayama rule for symmetric polynomials, `p_r · s_λ = ∑ (-1)^height s_μ` (the sum being
over the shapes `μ` obtained from `λ` by adding a ribbon of `r` boxes), into a recursion for the
values of the Schur class functions: removing a part `r` from the cycle type expresses `χ^μ` as the
signed sum of the `χ^λ` over the shapes `λ` obtained from `μ` by removing a ribbon of `r` boxes.

As a consequence the Schur class functions take integer values.

## Main results

* `Equiv.Perm.pProd_cycleTypeList_eq_sum_of_le` : the Frobenius character formula in any number
  `k ≥ n` of variables.
* `Equiv.Perm.schurChar_mnRule` : **the Murnaghan-Nakayama rule for characters**, with the
  ribbons described as in
  `Mathlib/RingTheory/MvPolynomial/Symmetric/Schur/MurnaghanNakayama.lean`.
* `Equiv.Perm.schurChar_mnRule_ribbon` : the same rule, with the sum indexed by the shapes `η`
  such that `μ / η` is a ribbon and the sign given by the number of its rows.
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
      = ∑ η : PartIdx n n, schurChar η σ • schurPoly (Fin k) ℚ η.1 := by
  refine eq_of_truncVars_eq (le_refl n) hnk
    (pProd_mem_symHomogeneousSubmodule (cycleTypeIdx hnk σ))
    (Submodule.sum_mem _ fun η _ => Submodule.smul_mem _ _
      (schurPoly_mem_symHomogeneousSubmodule
        (⟨η.1, η.2.1, η.2.2.1, η.2.2.2.trans hnk⟩ : PartIdx n k))) ?_
  rw [truncVars_pProd hnk (isPart_cycleTypeList σ), map_sum,
    pProd_cycleTypeList_eq_sum σ]
  refine Finset.sum_congr rfl fun η _ => ?_
  rw [map_smul, truncVars_schurPoly hnk η.2.1 (le_of_eq η.2.2.1)]

/-! ### The Murnaghan-Nakayama rule -/

/-- Adding a ribbon of `r` boxes to a partition of `n` gives a partition of `N = n + r`
with at most `N` parts. -/
lemma mnShapeIdx_aux (hr : 0 < r) (hN : n + r = N) (η : PartIdx n n) {k : ℕ} (hk : k < N)
    (hadd : MNAddable η.1 r k) :
    IsPart (mnShape η.1 r k) ∧ (mnShape η.1 r k).sum = N ∧
      (mnShape η.1 r k).length ≤ N := by
  refine ⟨isPart_mnShape η.2.1 hr hadd, ?_, ?_⟩
  · rw [sum_mnShape η.2.1 hr, η.2.2.1, hN]
  · exact (length_mnShape_le _ _ _).trans
      (max_le hk (η.2.2.2.trans (by omega)))

/-- Regrouping the shapes obtained by adding a ribbon: only the shape `mnShape η r k`
contributes to the sum over the partitions of `N`. -/
lemma sum_ite_mnShape_smul (hr : 0 < r) (hN : n + r = N) (η : PartIdx n n) {k : ℕ}
    (hk : k < N) (a : ℚ) :
    ∑ μ : PartIdx N N,
        (if MNAddable η.1 r k ∧ mnShape η.1 r k = μ.1 then a else 0)
          • schurPoly (Fin N) ℚ μ.1
      = if MNAddable η.1 r k then a • schurPoly (Fin N) ℚ (mnShape η.1 r k) else 0 := by
  classical
  by_cases hadd : MNAddable η.1 r k
  · rw [ite_eq_left hadd]
    set μ0 : PartIdx N N := ⟨mnShape η.1 r k, mnShapeIdx_aux hr hN η hk hadd⟩ with hμ0
    have h0 : ∀ μ ∈ (Finset.univ : Finset (PartIdx N N)), μ ≠ μ0 →
        (if MNAddable η.1 r k ∧ mnShape η.1 r k = μ.1 then a else 0)
          • schurPoly (Fin N) ℚ μ.1 = 0 := by
      intro μ _ hne
      rw [ite_eq_right (fun hcond => hne (Subtype.ext hcond.2.symm)), zero_smul]
    rw [Finset.sum_eq_single_of_mem μ0 (Finset.mem_univ _) h0, hμ0,
      ite_eq_left ⟨hadd, rfl⟩]
  · rw [ite_eq_right hadd]
    refine Finset.sum_eq_zero fun μ _ => ?_
    rw [ite_eq_right (fun hc => hadd hc.1), zero_smul]

/-- **The Murnaghan-Nakayama rule for the characters of the symmetric group**: if the cycle
type of `σ ∈ S_N` is obtained from the one of `τ ∈ S_n` by adding a part `r`, then the value
`χ^μ(σ)` is the signed sum of the values `χ^λ(τ)` over the shapes `λ` from which `μ` is
obtained by adding a ribbon of `r` boxes, the sign being `(-1)` to the height of the
ribbon. -/
theorem schurChar_mnRule (hr : 0 < r) (hN : n + r = N)
    (τ : Perm (Fin n)) (σ : Perm (Fin N))
    (hperm : (cycleTypeList σ).Perm (r :: cycleTypeList τ)) (μ : PartIdx N N) :
    schurChar μ σ
      = ∑ η : PartIdx n n, ∑ k : Fin N,
          if MNAddable η.1 r (k : ℕ) ∧ mnShape η.1 r (k : ℕ) = μ.1 then
            ((-1 : ℚ) ^ mnHeight η.1 r (k : ℕ)) * schurChar η τ else 0 := by
  classical
  have hle : n ≤ N := by omega
  set c : PartIdx N N → ℚ := fun ν => ∑ η : PartIdx n n, ∑ k : Fin N,
      if MNAddable η.1 r (k : ℕ) ∧ mnShape η.1 r (k : ℕ) = ν.1 then
        ((-1 : ℚ) ^ mnHeight η.1 r (k : ℕ)) * schurChar η τ else 0 with hc
  have key : ∑ ν : PartIdx N N, schurChar ν σ • schurPoly (Fin N) ℚ ν.1
      = ∑ ν : PartIdx N N, c ν • schurPoly (Fin N) ℚ ν.1 := by
    rw [← pProd_cycleTypeList_eq_sum σ, pProd_of_perm N ℚ hperm, pProd_cons,
      pProd_cycleTypeList_eq_sum_of_le hle τ, Finset.mul_sum]
    have hrhs : ∑ ν : PartIdx N N, c ν • schurPoly (Fin N) ℚ ν.1
        = ∑ η : PartIdx n n, ∑ k : Fin N,
            if MNAddable η.1 r (k : ℕ) then
              (((-1 : ℚ) ^ mnHeight η.1 r (k : ℕ)) * schurChar η τ)
                • schurPoly (Fin N) ℚ (mnShape η.1 r (k : ℕ))
            else 0 := by
      rw [hc]
      simp only [Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun η _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => sum_ite_mnShape_smul hr hN η k.isLt _
    rw [hrhs]
    refine Finset.sum_congr rfl fun η _ => ?_
    rw [mul_smul_comm, psum_mul_schurPoly η.2.1 (η.2.2.2.trans hle) hr, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hadd : MNAddable η.1 r (k : ℕ)
    · rw [ite_eq_left hadd, ite_eq_left hadd, smul_comm, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
      push_cast
      ring_nf
    · rw [ite_eq_right hadd, ite_eq_right hadd, smul_zero]
  have hzero : ∑ ν : PartIdx N N, (schurChar ν σ - c ν) • schurPoly (Fin N) ℚ ν.1 = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, key, sub_self]
  have hli := linearIndependent_schurPoly N N ℚ
  rw [Fintype.linearIndependent_iff] at hli
  exact sub_eq_zero.1 (hli _ hzero μ)

/-! ### The rule in the language of ribbons -/

open scoped Classical in
/-- The sum over the rows in which a ribbon can be added reduces to a single term: the
shape `μ` is reached exactly when `μ / η` is a ribbon, and then only from the row where
the ribbon stops. -/
lemma sum_ite_mnShape_eq_ite_ribbon {η μ : List ℕ} (hη : IsPart η) (hμ : IsPart μ)
    (hr : 0 < r) (hsum : μ.sum = η.sum + r) (hlen : μ.length ≤ N) (a : ℚ) :
    ∑ k : Fin N, (if MNAddable η r (k : ℕ) ∧ mnShape η r (k : ℕ) = μ then
        ((-1 : ℚ) ^ mnHeight η r (k : ℕ)) * a else 0)
      = if ∃ s k, RibbonOn s k η μ then ((-1 : ℚ) ^ (ribbonHeight η μ - 1)) * a
        else 0 := by
  classical
  by_cases hex : ∃ s k, RibbonOn s k η μ
  · obtain ⟨s, k, hrib⟩ := hex
    obtain ⟨-, hadd, hshape⟩ := mnShape_of_ribbonOn hη hμ hrib hr hsum
    have hk : k < N := lt_of_lt_of_le (lt_length_of_ribbonOn hη hrib) hlen
    rw [ite_eq_left ⟨s, k, hrib⟩]
    have hheight : ribbonHeight η μ - 1 = mnHeight η r k := by
      rw [← hshape, ribbonHeight_mnShape hη hr hadd, Nat.add_sub_cancel]
    rw [Finset.sum_eq_single_of_mem (⟨k, hk⟩ : Fin N) (Finset.mem_univ _) ?_,
      ite_eq_left ⟨hadd, hshape⟩, hheight]
    intro k' _ hne
    refine ite_eq_right fun hcond => hne (Fin.ext ?_)
    have hrib' : RibbonOn (mnPos η r (k' : ℕ)) (k' : ℕ) η μ := by
      rw [← hcond.2]
      exact ribbonOn_mnShape hη hr hcond.1
    exact (RibbonOn.unique hη hrib' hrib).2
  · rw [ite_eq_right hex]
    refine Finset.sum_eq_zero fun k _ => ite_eq_right fun hcond => hex ?_
    refine ⟨mnPos η r (k : ℕ), (k : ℕ), ?_⟩
    rw [← hcond.2]
    exact ribbonOn_mnShape hη hr hcond.1

open scoped Classical in
/-- **The Murnaghan-Nakayama rule for characters, in the language of ribbons**: if the
cycle type of `σ ∈ S_N` is obtained from the one of `τ ∈ S_n` by adding a part `r`, then
`χ^μ(σ)` is the sum of the values `χ^λ(τ)`, over the partitions `λ` of `n` such that the
skew shape `μ / λ` is a ribbon, with the sign `(-1)` to the number of rows of the ribbon
minus one. -/
theorem schurChar_mnRule_ribbon (hr : 0 < r) (hN : n + r = N)
    (τ : Perm (Fin n)) (σ : Perm (Fin N))
    (hperm : (cycleTypeList σ).Perm (r :: cycleTypeList τ)) (μ : PartIdx N N) :
    schurChar μ σ
      = ∑ η : PartIdx n n,
          if ∃ s k, RibbonOn s k η.1 μ.1 then
            ((-1 : ℚ) ^ (ribbonHeight η.1 μ.1 - 1)) * schurChar η τ else 0 := by
  classical
  rw [schurChar_mnRule hr hN τ σ hperm μ]
  refine Finset.sum_congr rfl fun η _ => ?_
  exact sum_ite_mnShape_eq_ite_ribbon η.2.1 μ.2.1 hr (by rw [μ.2.2.1, η.2.2.1, hN])
    μ.2.2.2 _

/-! ### The value at an `n`-cycle -/

/-- **The character of `S_n` at an `n`-cycle** vanishes unless the shape is a *hook*, that
is unless its second row has at most one box, in which case it is `(-1)` to the number of
rows of the shape minus one. -/
theorem schurChar_of_cycleTypeList_eq_singleton (hn : 0 < n) (σ : Perm (Fin n))
    (hsig : cycleTypeList σ = [n]) (μ : PartIdx n n) :
    schurChar μ σ = if μ.1.getD 1 0 ≤ 1 then (-1 : ℚ) ^ (μ.1.length - 1) else 0 := by
  classical
  have hne : μ.1 ≠ [] := by
    intro h
    have hsum := μ.2.2.1
    rw [h, List.sum_nil] at hsum
    omega
  have hperm : (cycleTypeList σ).Perm (n :: cycleTypeList (1 : Perm (Fin 0))) := by
    rw [hsig, cycleTypeList_one]
    simp
  rw [schurChar_mnRule_ribbon hn (Nat.zero_add n) (1 : Perm (Fin 0)) σ hperm μ]
  have hnil : IsPart ([] : List ℕ) := trivial
  set η0 : PartIdx 0 0 := ⟨[], hnil, rfl, le_refl 0⟩ with hη0
  rw [Finset.sum_eq_single_of_mem η0 (Finset.mem_univ _)
    (fun η _ hlne => absurd (Subtype.ext (η.2.1.eq_nil_of_sum_eq_zero η.2.2.1)) hlne)]
  have hchar : schurChar η0 (1 : Perm (Fin 0)) = 1 := by
    rw [schurChar_one]
    simp [hη0, numStdTab_nil]
  rw [hchar, mul_one, ribbonHeight_nil μ.2.1]
  exact if_congr (exists_ribbonOn_nil_iff μ.2.1 hne) rfl rfl

/-! ### Integrality of the character values -/

/-- The values of the Schur class functions lie in the subring of the integers. -/
lemma schurChar_mem_range_intCast (n : ℕ) (η : PartIdx n n) (σ : Perm (Fin n)) :
    schurChar η σ ∈ (Int.castRingHom ℚ).range := by
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
      exact ⟨(numStdTab η.1 : ℤ), rfl⟩
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
        (by rw [hct, hτ]) η]
      refine Subring.sum_mem _ fun μ _ => Subring.sum_mem _ fun k _ => ?_
      split
      · exact Subring.mul_mem _
          (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _)
          (ih rest.sum hlt μ τ)
      · exact Subring.zero_mem _

/-- **The values of the Schur class functions are integers.** -/
theorem exists_intCast_schurChar (η : PartIdx n n) (σ : Perm (Fin n)) :
    ∃ z : ℤ, schurChar η σ = (z : ℚ) := by
  obtain ⟨z, hz⟩ := schurChar_mem_range_intCast n η σ
  exact ⟨z, hz.symm⟩

end Equiv.Perm
