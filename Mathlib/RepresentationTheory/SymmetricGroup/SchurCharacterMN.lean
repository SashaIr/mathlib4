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
* `Equiv.Perm.schurChar_mnRule_ribbon` : the same rule, with the sum indexed by the shapes `lam`
  such that `mu / lam` is a ribbon and the sign given by the number of its rows.
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
theorem pProd_cycleTypeList_eq_sum_of_le (hnk : n ≤ k) (sigma : Perm (Fin n)) :
    pProd k ℚ (cycleTypeList sigma)
      = ∑ lam : PartIdx n n, schurChar lam sigma • schurPoly (Fin k) ℚ lam.1 := by
  refine eq_of_truncVars_eq (le_refl n) hnk
    (pProd_mem_symHomogeneousSubmodule (cycleTypeIdx hnk sigma))
    (Submodule.sum_mem _ fun lam _ => Submodule.smul_mem _ _
      (schurPoly_mem_symHomogeneousSubmodule
        (⟨lam.1, lam.2.1, lam.2.2.1, lam.2.2.2.trans hnk⟩ : PartIdx n k))) ?_
  rw [truncVars_pProd hnk (isPart_cycleTypeList sigma), map_sum,
    pProd_cycleTypeList_eq_sum sigma]
  refine Finset.sum_congr rfl fun lam _ => ?_
  rw [map_smul, truncVars_schurPoly hnk lam.2.1 (le_of_eq lam.2.2.1)]

/-! ### The Murnaghan-Nakayama rule -/

/-- Adding a ribbon of `r` boxes to a partition of `n` gives a partition of `N = n + r`
with at most `N` parts. -/
lemma mnShapeIdx_aux (hr : 0 < r) (hN : n + r = N) (lam : PartIdx n n) {k : ℕ} (hk : k < N)
    (hadd : MNAddable lam.1 r k) :
    IsPart (mnShape lam.1 r k) ∧ (mnShape lam.1 r k).sum = N ∧
      (mnShape lam.1 r k).length ≤ N := by
  refine ⟨isPart_mnShape lam.2.1 hr hadd, ?_, ?_⟩
  · rw [sum_mnShape lam.2.1 hr, lam.2.2.1, hN]
  · exact (length_mnShape_le _ _ _).trans
      (max_le hk (lam.2.2.2.trans (by omega)))

/-- Regrouping the shapes obtained by adding a ribbon: only the shape `mnShape lam r k`
contributes to the sum over the partitions of `N`. -/
lemma sum_ite_mnShape_smul (hr : 0 < r) (hN : n + r = N) (lam : PartIdx n n) {k : ℕ}
    (hk : k < N) (a : ℚ) :
    ∑ mu : PartIdx N N,
        (if MNAddable lam.1 r k ∧ mnShape lam.1 r k = mu.1 then a else 0)
          • schurPoly (Fin N) ℚ mu.1
      = if MNAddable lam.1 r k then a • schurPoly (Fin N) ℚ (mnShape lam.1 r k) else 0 := by
  classical
  by_cases hadd : MNAddable lam.1 r k
  · rw [ite_eq_left hadd]
    set mu0 : PartIdx N N := ⟨mnShape lam.1 r k, mnShapeIdx_aux hr hN lam hk hadd⟩ with hmu0
    have h0 : ∀ mu ∈ (Finset.univ : Finset (PartIdx N N)), mu ≠ mu0 →
        (if MNAddable lam.1 r k ∧ mnShape lam.1 r k = mu.1 then a else 0)
          • schurPoly (Fin N) ℚ mu.1 = 0 := by
      intro mu _ hne
      rw [ite_eq_right (fun hcond => hne (Subtype.ext hcond.2.symm)), zero_smul]
    rw [Finset.sum_eq_single_of_mem mu0 (Finset.mem_univ _) h0, hmu0,
      ite_eq_left ⟨hadd, rfl⟩]
  · rw [ite_eq_right hadd]
    refine Finset.sum_eq_zero fun mu _ => ?_
    rw [ite_eq_right (fun hc => hadd hc.1), zero_smul]

/-- **The Murnaghan-Nakayama rule for the characters of the symmetric group**: if the cycle
type of `σ ∈ S_N` is obtained from the one of `τ ∈ S_n` by adding a part `r`, then the value
`χ^μ(σ)` is the signed sum of the values `χ^λ(τ)` over the shapes `λ` from which `μ` is
obtained by adding a ribbon of `r` boxes, the sign being `(-1)` to the height of the
ribbon. -/
theorem schurChar_mnRule (hr : 0 < r) (hN : n + r = N)
    (tau : Perm (Fin n)) (sigma : Perm (Fin N))
    (hperm : (cycleTypeList sigma).Perm (r :: cycleTypeList tau)) (mu : PartIdx N N) :
    schurChar mu sigma
      = ∑ lam : PartIdx n n, ∑ k : Fin N,
          if MNAddable lam.1 r (k : ℕ) ∧ mnShape lam.1 r (k : ℕ) = mu.1 then
            ((-1 : ℚ) ^ mnHeight lam.1 r (k : ℕ)) * schurChar lam tau else 0 := by
  classical
  have hle : n ≤ N := by omega
  set c : PartIdx N N → ℚ := fun nu => ∑ lam : PartIdx n n, ∑ k : Fin N,
      if MNAddable lam.1 r (k : ℕ) ∧ mnShape lam.1 r (k : ℕ) = nu.1 then
        ((-1 : ℚ) ^ mnHeight lam.1 r (k : ℕ)) * schurChar lam tau else 0 with hc
  have key : ∑ nu : PartIdx N N, schurChar nu sigma • schurPoly (Fin N) ℚ nu.1
      = ∑ nu : PartIdx N N, c nu • schurPoly (Fin N) ℚ nu.1 := by
    rw [← pProd_cycleTypeList_eq_sum sigma, pProd_of_perm N ℚ hperm, pProd_cons,
      pProd_cycleTypeList_eq_sum_of_le hle tau, Finset.mul_sum]
    have hrhs : ∑ nu : PartIdx N N, c nu • schurPoly (Fin N) ℚ nu.1
        = ∑ lam : PartIdx n n, ∑ k : Fin N,
            if MNAddable lam.1 r (k : ℕ) then
              (((-1 : ℚ) ^ mnHeight lam.1 r (k : ℕ)) * schurChar lam tau)
                • schurPoly (Fin N) ℚ (mnShape lam.1 r (k : ℕ))
            else 0 := by
      rw [hc]
      simp only [Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun lam _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => sum_ite_mnShape_smul hr hN lam k.isLt _
    rw [hrhs]
    refine Finset.sum_congr rfl fun lam _ => ?_
    rw [mul_smul_comm, psum_mul_schurPoly lam.2.1 (lam.2.2.2.trans hle) hr, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hadd : MNAddable lam.1 r (k : ℕ)
    · rw [ite_eq_left hadd, ite_eq_left hadd, smul_comm, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
      push_cast
      ring_nf
    · rw [ite_eq_right hadd, ite_eq_right hadd, smul_zero]
  have hzero : ∑ nu : PartIdx N N, (schurChar nu sigma - c nu) • schurPoly (Fin N) ℚ nu.1 = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, key, sub_self]
  have hli := linearIndependent_schurPoly N N ℚ
  rw [Fintype.linearIndependent_iff] at hli
  exact sub_eq_zero.1 (hli _ hzero mu)

/-! ### The rule in the language of ribbons -/

open scoped Classical in
/-- The sum over the rows in which a ribbon can be added reduces to a single term: the
shape `mu` is reached exactly when `mu / lam` is a ribbon, and then only from the row where
the ribbon stops. -/
lemma sum_ite_mnShape_eq_ite_ribbon {lam mu : List ℕ} (hlam : IsPart lam) (hmu : IsPart mu)
    (hr : 0 < r) (hsum : mu.sum = lam.sum + r) (hlen : mu.length ≤ N) (a : ℚ) :
    ∑ k : Fin N, (if MNAddable lam r (k : ℕ) ∧ mnShape lam r (k : ℕ) = mu then
        ((-1 : ℚ) ^ mnHeight lam r (k : ℕ)) * a else 0)
      = if ∃ s k, RibbonOn s k lam mu then ((-1 : ℚ) ^ (ribbonHeight lam mu - 1)) * a
        else 0 := by
  classical
  by_cases hex : ∃ s k, RibbonOn s k lam mu
  · obtain ⟨s, k, hrib⟩ := hex
    obtain ⟨-, hadd, hshape⟩ := mnShape_of_ribbonOn hlam hmu hrib hr hsum
    have hk : k < N := lt_of_lt_of_le (lt_length_of_ribbonOn hlam hrib) hlen
    rw [ite_eq_left ⟨s, k, hrib⟩]
    have hheight : ribbonHeight lam mu - 1 = mnHeight lam r k := by
      rw [← hshape, ribbonHeight_mnShape hlam hr hadd, Nat.add_sub_cancel]
    rw [Finset.sum_eq_single_of_mem (⟨k, hk⟩ : Fin N) (Finset.mem_univ _) ?_,
      ite_eq_left ⟨hadd, hshape⟩, hheight]
    intro k' _ hne
    refine ite_eq_right fun hcond => hne (Fin.ext ?_)
    have hrib' : RibbonOn (mnPos lam r (k' : ℕ)) (k' : ℕ) lam mu := by
      rw [← hcond.2]
      exact ribbonOn_mnShape hlam hr hcond.1
    exact (RibbonOn.unique hlam hrib' hrib).2
  · rw [ite_eq_right hex]
    refine Finset.sum_eq_zero fun k _ => ite_eq_right fun hcond => hex ?_
    refine ⟨mnPos lam r (k : ℕ), (k : ℕ), ?_⟩
    rw [← hcond.2]
    exact ribbonOn_mnShape hlam hr hcond.1

open scoped Classical in
/-- **The Murnaghan-Nakayama rule for characters, in the language of ribbons**: if the
cycle type of `σ ∈ S_N` is obtained from the one of `τ ∈ S_n` by adding a part `r`, then
`χ^μ(σ)` is the sum of the values `χ^λ(τ)`, over the partitions `λ` of `n` such that the
skew shape `μ / λ` is a ribbon, with the sign `(-1)` to the number of rows of the ribbon
minus one. -/
theorem schurChar_mnRule_ribbon (hr : 0 < r) (hN : n + r = N)
    (tau : Perm (Fin n)) (sigma : Perm (Fin N))
    (hperm : (cycleTypeList sigma).Perm (r :: cycleTypeList tau)) (mu : PartIdx N N) :
    schurChar mu sigma
      = ∑ lam : PartIdx n n,
          if ∃ s k, RibbonOn s k lam.1 mu.1 then
            ((-1 : ℚ) ^ (ribbonHeight lam.1 mu.1 - 1)) * schurChar lam tau else 0 := by
  classical
  rw [schurChar_mnRule hr hN tau sigma hperm mu]
  refine Finset.sum_congr rfl fun lam _ => ?_
  exact sum_ite_mnShape_eq_ite_ribbon lam.2.1 mu.2.1 hr (by rw [mu.2.2.1, lam.2.2.1, hN])
    mu.2.2.2 _

/-! ### The value at an `n`-cycle -/

/-- **The character of `S_n` at an `n`-cycle** vanishes unless the shape is a *hook*, that
is unless its second row has at most one box, in which case it is `(-1)` to the number of
rows of the shape minus one. -/
theorem schurChar_of_cycleTypeList_eq_singleton (hn : 0 < n) (sigma : Perm (Fin n))
    (hsig : cycleTypeList sigma = [n]) (mu : PartIdx n n) :
    schurChar mu sigma = if mu.1.getD 1 0 ≤ 1 then (-1 : ℚ) ^ (mu.1.length - 1) else 0 := by
  classical
  have hne : mu.1 ≠ [] := by
    intro h
    have hsum := mu.2.2.1
    rw [h, List.sum_nil] at hsum
    omega
  have hperm : (cycleTypeList sigma).Perm (n :: cycleTypeList (1 : Perm (Fin 0))) := by
    rw [hsig, cycleTypeList_one]
    simp
  rw [schurChar_mnRule_ribbon hn (Nat.zero_add n) (1 : Perm (Fin 0)) sigma hperm mu]
  have hnil : IsPart ([] : List ℕ) := trivial
  set lam0 : PartIdx 0 0 := ⟨[], hnil, rfl, le_refl 0⟩ with hlam0
  rw [Finset.sum_eq_single_of_mem lam0 (Finset.mem_univ _)
    (fun lam _ hlne => absurd (Subtype.ext (lam.2.1.eq_nil_of_sum_eq_zero lam.2.2.1)) hlne)]
  have hchar : schurChar lam0 (1 : Perm (Fin 0)) = 1 := by
    rw [schurChar_one]
    simp [hlam0, numStdTab_nil]
  rw [hchar, mul_one, ribbonHeight_nil mu.2.1]
  exact if_congr (exists_ribbonOn_nil_iff mu.2.1 hne) rfl rfl

/-! ### Integrality of the character values -/

/-- The values of the Schur class functions lie in the subring of the integers. -/
lemma schurChar_mem_range_intCast (n : ℕ) (lam : PartIdx n n) (sigma : Perm (Fin n)) :
    schurChar lam sigma ∈ (Int.castRingHom ℚ).range := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match hct : cycleTypeList sigma with
    | [] =>
      have hn : n = 0 := by
        have hsum := sum_cycleTypeList sigma
        rw [hct] at hsum
        simpa using hsum.symm
      subst hn
      rw [Subsingleton.elim sigma 1, schurChar_one]
      exact ⟨(numStdTab lam.1 : ℤ), rfl⟩
    | r :: rest =>
      have hpart : IsPart (r :: rest) := hct ▸ isPart_cycleTypeList sigma
      have hr : 0 < r := hpart.pos_of_mem (List.mem_cons_self ..)
      have hsum : r + rest.sum = n := by
        have hsum := sum_cycleTypeList sigma
        rw [hct] at hsum
        simpa using hsum
      obtain ⟨tau, htau⟩ := exists_cycleTypeList_eq (n := rest.sum) hpart.of_cons rfl
      have hlt : rest.sum < n := by omega
      rw [schurChar_mnRule hr (show rest.sum + r = n by omega) tau sigma
        (by rw [hct, htau]) lam]
      refine Subring.sum_mem _ fun mu _ => Subring.sum_mem _ fun k _ => ?_
      split
      · exact Subring.mul_mem _
          (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _)
          (ih rest.sum hlt mu tau)
      · exact Subring.zero_mem _

/-- **The values of the Schur class functions are integers.** -/
theorem exists_intCast_schurChar (lam : PartIdx n n) (sigma : Perm (Fin n)) :
    ∃ z : ℤ, schurChar lam sigma = (z : ℚ) := by
  obtain ⟨z, hz⟩ := schurChar_mem_range_intCast n lam sigma
  exact ⟨z, hz.symm⟩

end Equiv.Perm
