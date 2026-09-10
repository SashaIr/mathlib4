/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Basis.Monomial

/-!
# The monomial symmetric polynomials agree with those of Mathlib

Mathlib defines the monomial symmetric polynomials `MvPolynomial.msymm σ R μ` indexed by a
partition `μ` of `n` in Mathlib's sense (a multiset of positive parts).  This file
identifies them with the monomial symmetric polynomials `MvPolynomial.monomialSym` of this
development, which are indexed by the list-based partitions of Coq-Combi.

## Main results

* `MvPolynomial.coeff_msymm` : the coefficients of `msymm` are `1` on the monomials whose shape is
  the given partition, and `0` elsewhere.
* `MvPolynomial.monomialSym_eq_msymm` : the two definitions agree.
-/

@[expose] public section

open Young

namespace MvPolynomial

open List MvPolynomial

variable {m : ℕ} {R : Type*} [CommSemiring R]

/-! ### The shape of a monomial as a multiset -/

/-- The parts of the shape of a monomial are its nonzero exponents. -/
lemma coe_degShape (d : Fin m →₀ ℕ) :
    (degShape d : Multiset ℕ) = Multiset.map d d.support.val := by
  classical
  have hsplit : ((degSorted d : List ℕ) : Multiset ℕ)
      = ((degShape d : List ℕ) : Multiset ℕ)
        + (((degSorted d).rtakeWhile (fun x => x == 0) : List ℕ) : Multiset ℕ) := by
    conv_lhs => rw [← trimZeros_append (degSorted d)]
    rfl
  have hzeros : Multiset.filter (fun x : ℕ => x ≠ 0)
      (((degSorted d).rtakeWhile (fun x => x == 0) : List ℕ) : Multiset ℕ) = 0 := by
    refine Multiset.filter_eq_nil.2 fun x hx => ?_
    simpa using mem_rtakeWhile_zero (by simpa using hx)
  have hpart : Multiset.filter (fun x : ℕ => x ≠ 0) ((degShape d : List ℕ) : Multiset ℕ)
      = ((degShape d : List ℕ) : Multiset ℕ) := by
    refine Multiset.filter_eq_self.2 fun x hx => ?_
    exact (isPart_degShape d).pos_of_mem (by simpa using hx) |>.ne'
  have hleft : Multiset.filter (fun x : ℕ => x ≠ 0) (degMultiset d)
      = ((degShape d : List ℕ) : Multiset ℕ) := by
    rw [← coe_degSorted, hsplit, Multiset.filter_add, hzeros, hpart, add_zero]
  have hright : Multiset.filter (fun x : ℕ => x ≠ 0) (degMultiset d)
      = Multiset.map d d.support.val := by
    have hsupp : Multiset.filter (fun i : Fin m => d i ≠ 0) Finset.univ.val
        = d.support.val := by
      rw [← Finset.filter_val]
      refine congrArg Finset.val ?_
      ext i
      simp [Finsupp.mem_support_iff]
    rw [degMultiset, Multiset.filter_map, ← hsupp]
    rfl
  rw [← hleft, hright]

/-! ### The coefficients of Mathlib's monomial symmetric polynomials -/

lemma prod_map_X_multiset (s : Multiset (Fin m)) :
    ((s.map (X : Fin m → MvPolynomial (Fin m) R)).prod)
      = monomial (Multiset.toFinsupp s) 1 := by
  induction s using Quotient.inductionOn with
  | _ l => exact prod_map_X l

/-- The coefficient of a monomial in `msymm` is `1` if the shape of the monomial is the
given partition, and `0` otherwise. -/
theorem coeff_msymm {n : ℕ} (mu : Nat.Partition n) (d : Fin m →₀ ℕ) :
    coeff d (msymm (Fin m) R mu)
      = if (degShape d : Multiset ℕ) = mu.parts then 1 else 0 := by
  classical
  have hshape : ∀ a : Sym (Fin m) n, Multiset.toFinsupp a.1 = d →
      (Nat.Partition.ofSym a).parts = (degShape d : Multiset ℕ) := by
    intro a ha
    have hval : a.1 = Finsupp.toMultiset d := by
      rw [← ha, Multiset.toFinsupp_toMultiset]
    have : (Nat.Partition.ofSym a).parts = Multiset.map d d.support.val := by
      rw [show (Nat.Partition.ofSym a).parts = a.1.dedup.map a.1.count from rfl, hval]
      have hdedup : (Finsupp.toMultiset d).dedup = d.support.val := by
        rw [← Finsupp.toFinset_toMultiset d]
        rfl
      rw [hdedup]
      exact Multiset.map_congr rfl fun i _ => Finsupp.count_toMultiset d i
    rw [this, coe_degShape]
  rw [msymm, coeff_sum]
  simp only [prod_map_X_multiset, coeff_monomial]
  by_cases hd : (degShape d : Multiset ℕ) = mu.parts
  · rw [ite_eq_left hd]
    have hcard : Multiset.card (Finsupp.toMultiset d) = n := by
      have hsum : (Finsupp.toMultiset d).card = (degShape d).sum := by
        rw [Finsupp.card_toMultiset, sum_degShape d, Finsupp.sum]
        simp only [id]
        exact Finset.sum_subset (Finset.subset_univ d.support)
          fun i _ hi => by simpa using hi
      rw [hsum, ← Multiset.sum_coe, hd, mu.parts_sum]
    set a0 : {a : Sym (Fin m) n // Nat.Partition.ofSym a = mu} :=
      ⟨⟨Finsupp.toMultiset d, hcard⟩, by
        refine Nat.Partition.ext ?_
        rw [hshape ⟨Finsupp.toMultiset d, hcard⟩ (by simp), hd]⟩ with ha0
    rw [Fintype.sum_eq_single a0]
    · rw [ite_eq_left (by simp [ha0])]
    · intro b hb
      refine ite_eq_right fun hbd => hb (Subtype.ext (Sym.ext ?_))
      rw [ha0]
      simpa using congrArg Finsupp.toMultiset hbd
  · rw [ite_eq_right hd, Finset.sum_eq_zero]
    intro a _
    refine ite_eq_right fun hbd => hd ?_
    rw [← hshape a.1 hbd, a.2]

/-- **The two definitions of the monomial symmetric polynomials agree**: the monomial
symmetric polynomial of a partition `lam` with at most `m` parts is Mathlib's `msymm` of
the corresponding partition of `|lam|`. -/
theorem monomialSym_eq_msymm {n : ℕ} {lam : List ℕ} (hlam : IsPart lam) (hsum : lam.sum = n)
    (hlen : lam.length ≤ m) :
    monomialSym m R lam = msymm (Fin m) R (listPartEquivNatPartition n ⟨lam, hlam, hsum⟩) := by
  classical
  refine MvPolynomial.ext _ _ fun d => ?_
  rw [coeff_monomialSym, coeff_msymm, listPartEquivNatPartition_apply]
  have hiff : d ∈ degOrbit (shapeContent m lam)
      ↔ (degShape d : Multiset ℕ) = (lam : Multiset ℕ) := by
    rw [mem_degOrbit_iff, ← degShape_eq_iff, degShape_shapeContent hlam hlen]
    constructor
    · intro h; rw [h]
    · intro h
      have := congrArg sortDesc h
      rwa [sortDesc_coe (isPart_degShape d), sortDesc_coe hlam] at this
  by_cases hd : d ∈ degOrbit (shapeContent m lam)
  · rw [ite_eq_left hd, ite_eq_left (hiff.1 hd)]
  · rw [ite_eq_right hd, ite_eq_right fun h => hd (hiff.2 h)]

end MvPolynomial
