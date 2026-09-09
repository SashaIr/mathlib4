/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Order.Interval.Finset.Nat

/-!
# The rank function of a permutation

Following `theories/SymGroup/Bruhat.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we attach to a permutation `s` of
`Fin n` its *rank function* `permRank s i j`, the number of `k < i` with `s k < j`.  In
the Coq development this is the matrix `mxsum (perm_mx s)` of partial sums of the
permutation matrix of `s`; it is the basic tool used there to define the (strong) Bruhat
order, which is done in `Mathlib/GroupTheory/Perm/SymmetricGroup/Bruhat.lean`.

## Main definitions and results

* `Equiv.Perm.permRank s i j` : the number of `k < i` with `s k < j` (Coq
  `mxsum (perm_mx s) i j`).
* `Equiv.Perm.permRank_succ_left`, `Equiv.Perm.permRank_succ_right` : the increments of the rank
  function in each of its two arguments.
* `Equiv.Perm.permRank_injective` : a permutation is determined by its rank function (Coq
  `perm_mxsum_inj`).
* `Equiv.Perm.permRank_one`, `Equiv.Perm.permRank_revPerm` : the rank functions of the identity and
  of the longest element (Coq `perm_mxsum1` and `perm_mxsum_maxperm`).
* `Equiv.Perm.permRank_inv` : the rank function of `s⁻¹` is that of `s` with its two arguments
  exchanged (Coq `mxsum_tr` together with `tr_perm_mx`).
* `Equiv.Perm.permRank_revPerm_mul`, `Equiv.Perm.permRank_mul_revPerm` : the rank functions of
  `Fin.revPerm * s` and of `s * Fin.revPerm`.
-/

@[expose] public section

open Equiv Finset

namespace Equiv.Perm


variable {n : ℕ}

/-- The rank function of a permutation: `permRank s i j` is the number of `k < i` with
`s k < j`.  This is the Coq matrix `mxsum (perm_mx s) i j`. -/
def permRank (s : Perm (Fin n)) (i j : ℕ) : ℕ :=
  #{k ∈ (univ : Finset (Fin n)) | k.val < i ∧ (s k).val < j}

@[simp] lemma permRank_zero_left (s : Perm (Fin n)) (j : ℕ) : permRank s 0 j = 0 := by
  simp [permRank]

@[simp] lemma permRank_zero_right (s : Perm (Fin n)) (i : ℕ) : permRank s i 0 = 0 := by
  simp [permRank]

/-- Increasing the first argument of the rank function by one. -/
lemma permRank_succ_left (s : Perm (Fin n)) (i j : ℕ) :
    permRank s (i + 1) j
      = permRank s i j + if h : i < n then (if (s ⟨i, h⟩).val < j then 1 else 0) else 0 := by
  classical
  by_cases h : i < n
  · have hsplit : {k ∈ (univ : Finset (Fin n)) | k.val < i + 1 ∧ (s k).val < j}
        = {k ∈ (univ : Finset (Fin n)) | k.val < i ∧ (s k).val < j}
          ∪ {k ∈ (univ : Finset (Fin n)) | k.val = i ∧ (s k).val < j} := by
      ext k
      simp only [mem_filter, mem_univ, true_and, mem_union]
      omega
    have hdisj : Disjoint {k ∈ (univ : Finset (Fin n)) | k.val < i ∧ (s k).val < j}
        {k ∈ (univ : Finset (Fin n)) | k.val = i ∧ (s k).val < j} := by
      rw [Finset.disjoint_left]
      intro k hk hk'
      simp only [mem_filter, mem_univ, true_and] at hk hk'
      omega
    have hsingle : {k ∈ (univ : Finset (Fin n)) | k.val = i ∧ (s k).val < j}
        = if (s ⟨i, h⟩).val < j then {(⟨i, h⟩ : Fin n)} else ∅ := by
      ext k
      simp only [mem_filter, mem_univ, true_and]
      by_cases hs : (s ⟨i, h⟩).val < j
      · simp only [hs, ite_true, mem_singleton]
        constructor
        · rintro ⟨hk, -⟩
          exact Fin.ext hk
        · rintro rfl
          exact ⟨rfl, hs⟩
      · simp only [hs, ite_false, Finset.notMem_empty, iff_false, not_and]
        intro hk
        have hk' : k = (⟨i, h⟩ : Fin n) := Fin.ext hk
        subst hk'
        exact hs
    rw [permRank, permRank, hsplit, Finset.card_union_of_disjoint hdisj, hsingle, dite_eq_left h]
    by_cases hs : (s ⟨i, h⟩).val < j <;> simp [hs]
  · have hiff : ∀ k : Fin n, (k.val < i + 1 ∧ (s k).val < j) ↔ (k.val < i ∧ (s k).val < j) := by
      intro k
      have := k.isLt
      omega
    simp only [permRank, dite_eq_right h, add_zero]
    exact congrArg _ (Finset.filter_congr fun k _ => by simpa using hiff k)

/-- The rank function of `s⁻¹` is that of `s` with the two arguments exchanged. -/
lemma permRank_inv (s : Perm (Fin n)) (i j : ℕ) : permRank s⁻¹ i j = permRank s j i := by
  refine Finset.card_equiv s⁻¹ fun k => ?_
  have hk : s (s⁻¹ k) = k := by simp
  simp only [mem_filter, mem_univ, true_and, hk]
  exact and_comm

/-- Increasing the second argument of the rank function by one. -/
lemma permRank_succ_right (s : Perm (Fin n)) (i j : ℕ) :
    permRank s i (j + 1)
      = permRank s i j + if h : j < n then (if (s⁻¹ ⟨j, h⟩).val < i then 1 else 0) else 0 := by
  rw [← permRank_inv s (j + 1) i, ← permRank_inv s j i, permRank_succ_left]

/-- The rank function is bounded by its first argument. -/
lemma permRank_le_left (s : Perm (Fin n)) (i j : ℕ) : permRank s i j ≤ min i n := by
  rw [min_comm, ← Fin.card_filter_val_lt]
  refine Finset.card_le_card fun k hk => ?_
  simp only [mem_filter, mem_univ, true_and] at hk ⊢
  exact hk.1

/-- The rank function is bounded by its second argument. -/
lemma permRank_le_right (s : Perm (Fin n)) (i j : ℕ) : permRank s i j ≤ min j n := by
  rw [← permRank_inv s j i]
  exact permRank_le_left _ _ _

/-- The rank function is monotone in its first argument. -/
lemma permRank_mono_left (s : Perm (Fin n)) {i i' : ℕ} (h : i ≤ i') (j : ℕ) :
    permRank s i j ≤ permRank s i' j := by
  refine Finset.card_le_card fun k hk => ?_
  simp only [mem_filter, mem_univ, true_and] at hk ⊢
  exact ⟨lt_of_lt_of_le hk.1 h, hk.2⟩

/-- The rank function is monotone in its second argument. -/
lemma permRank_mono_right (s : Perm (Fin n)) (i : ℕ) {j j' : ℕ} (h : j ≤ j') :
    permRank s i j ≤ permRank s i j' := by
  rw [← permRank_inv s j i, ← permRank_inv s j' i]
  exact permRank_mono_left _ h _

/-- Beyond `n`, the first argument of the rank function may be replaced by `n`. -/
lemma permRank_of_le_left (s : Perm (Fin n)) {i : ℕ} (hi : n ≤ i) (j : ℕ) :
    permRank s i j = permRank s n j := by
  refine congrArg _ (Finset.filter_congr fun k _ => ?_)
  have := k.isLt
  simp only [and_congr_left_iff]
  omega

/-- Beyond `n`, the second argument of the rank function may be replaced by `n`. -/
lemma permRank_of_le_right (s : Perm (Fin n)) (i : ℕ) {j : ℕ} (hj : n ≤ j) :
    permRank s i j = permRank s i n := by
  rw [← permRank_inv s j i, ← permRank_inv s n i]
  exact permRank_of_le_left _ hj _

/-- Truncating the first argument of the rank function at `n` does not change it. -/
@[simp] lemma permRank_min_left (s : Perm (Fin n)) (i j : ℕ) :
    permRank s (min i n) j = permRank s i j := by
  rcases le_total i n with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, permRank_of_le_left s h]

/-- Truncating the second argument of the rank function at `n` does not change it. -/
@[simp] lemma permRank_min_right (s : Perm (Fin n)) (i j : ℕ) :
    permRank s i (min j n) = permRank s i j := by
  rcases le_total j n with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, permRank_of_le_right s i h]

@[simp] lemma permRank_top_left (s : Perm (Fin n)) (j : ℕ) : permRank s n j = min j n := by
  rw [permRank, min_comm, ← Fin.card_filter_val_lt]
  refine Finset.card_equiv s fun k => ?_
  simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
  exact fun _ => k.isLt

@[simp] lemma permRank_top_right (s : Perm (Fin n)) (i : ℕ) : permRank s i n = min i n := by
  rw [← permRank_inv s n i, permRank_top_left]

/-- The inclusion-exclusion lower bound on the rank function. -/
lemma le_permRank_add (s : Perm (Fin n)) (i j : ℕ) :
    min i n + min j n ≤ permRank s i j + n := by
  classical
  set A : Finset (Fin n) := {k ∈ (univ : Finset (Fin n)) | k.val < i} with hA
  set B : Finset (Fin n) := {k ∈ (univ : Finset (Fin n)) | (s k).val < j} with hB
  have hcardA : #A = min i n := Fin.card_filter_val_lt.trans (min_comm n i)
  have hcardB : #B = min j n := by
    rw [hB, ← permRank_top_left s j, permRank]
    exact congrArg _ (Finset.filter_congr fun k _ => by simp [k.isLt])
  have hinter : A ∩ B = {k ∈ (univ : Finset (Fin n)) | k.val < i ∧ (s k).val < j} := by
    ext k; simp [hA, hB]
  have hcards := Finset.card_union_add_card_inter A B
  have hle : #(A ∪ B) ≤ n := by
    simpa using Finset.card_le_univ (A ∪ B)
  rw [hcardA, hcardB, hinter] at hcards
  rw [permRank]
  omega

/-- The rank function of the identity (Coq `perm_mxsum1`). -/
lemma permRank_one (i j : ℕ) : permRank (1 : Perm (Fin n)) i j = min (min i j) n := by
  rw [permRank, min_comm, ← Fin.card_filter_val_lt]
  exact congrArg _ (Finset.filter_congr fun k _ => by simp)

/-- The rank function of the longest element (Coq `perm_mxsum_maxperm`). -/
lemma permRank_revPerm (i j : ℕ) :
    permRank (Fin.revPerm : Perm (Fin n)) i j = min i n + min j n - n := by
  rw [permRank]
  have hfilter : {k ∈ (univ : Finset (Fin n)) | k.val < i ∧
      ((Fin.revPerm : Perm (Fin n)) k).val < j}
      = {k ∈ (univ : Finset (Fin n)) | k.val < i ∧ n - j ≤ k.val} := by
    refine Finset.filter_congr fun k _ => ?_
    have hk := k.isLt
    simp only [Fin.revPerm_apply, Fin.val_rev, and_congr_right_iff]
    omega
  rw [hfilter]
  have hmap : ({k ∈ (univ : Finset (Fin n)) | k.val < i ∧ n - j ≤ k.val}).map
      ⟨Fin.val, Fin.val_injective⟩ = {x ∈ range n | x < i ∧ n - j ≤ x} := by
    ext x
    simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coeFn_mk, mem_range]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k.isLt, hk⟩
    · rintro ⟨hx, hxm⟩
      exact ⟨⟨x, hx⟩, hxm, rfl⟩
  rw [← Finset.card_map ⟨Fin.val, Fin.val_injective⟩, hmap,
    show {x ∈ range n | x < i ∧ n - j ≤ x} = Finset.Ico (n - j) (min i n) by
      ext x; simp [Finset.mem_Ico]; omega,
    Nat.card_Ico]
  omega

/-- A permutation is determined by its rank function (Coq `perm_mxsum_inj`). -/
lemma permRank_injective : Function.Injective (permRank (n := n)) := by
  intro s t hst
  ext k
  have hk : k.val < n := k.isLt
  have key : ∀ j : ℕ, (if (s ⟨k.val, hk⟩).val < j then 1 else 0)
      = (if (t ⟨k.val, hk⟩).val < j then (1 : ℕ) else 0) := by
    intro j
    have h1 := permRank_succ_left s k.val j
    have h2 := permRank_succ_left t k.val j
    rw [dite_eq_left hk] at h1 h2
    rw [hst] at h1
    omega
  have hks : (⟨k.val, hk⟩ : Fin n) = k := Fin.ext rfl
  rw [hks] at key
  have h1 := key (s k).val
  have h2 := key ((s k).val + 1)
  simp only [lt_irrefl, ite_false, Nat.lt_succ_self, ite_true] at h1 h2
  have hval : (t k).val = (s k).val := by
    by_cases hlt : (t k).val < (s k).val
    · rw [ite_eq_left hlt] at h1; omega
    · push Not at hlt
      by_cases hgt : (s k).val < (t k).val
      · rw [ite_eq_right (by omega)] at h2; omega
      · omega
  exact hval.symm

/-- The rank function of `Fin.revPerm * s` (Coq `mxsum_maxpermM`). -/
lemma permRank_revPerm_mul (s : Perm (Fin n)) (i j : ℕ) :
    permRank ((Fin.revPerm : Perm (Fin n)) * s) i j = min i n - permRank s i (n - j) := by
  classical
  have hle : permRank s i (n - j) ≤ min i n := permRank_le_left _ _ _
  have hsplit : permRank s i (n - j)
      + permRank ((Fin.revPerm : Perm (Fin n)) * s) i j = min i n := by
    rw [permRank, permRank, min_comm, ← Fin.card_filter_val_lt, ← Finset.card_union_of_disjoint]
    · congr 1
      ext k
      have hk := (s k).isLt
      simp only [mem_union, mem_filter, mem_univ, true_and, Perm.mul_apply, Fin.revPerm_apply,
        Fin.val_rev]
      omega
    · rw [Finset.disjoint_left]
      intro k hk hk'
      simp only [mem_filter, mem_univ, true_and, Perm.mul_apply, Fin.revPerm_apply,
        Fin.val_rev] at hk hk'
      have hk2 := (s k).isLt
      omega
  omega

/-- The rank function of `s * Fin.revPerm`. -/
lemma permRank_mul_revPerm (s : Perm (Fin n)) (i j : ℕ) :
    permRank (s * (Fin.revPerm : Perm (Fin n))) i j = min j n - permRank s (n - i) j := by
  have hinv : (s * (Fin.revPerm : Perm (Fin n)))⁻¹ = (Fin.revPerm : Perm (Fin n)) * s⁻¹ := by
    rw [mul_inv_rev, show (Fin.revPerm : Perm (Fin n))⁻¹ = Fin.revPerm from Equiv.coe_inj.mp rfl]
  rw [← permRank_inv (s * (Fin.revPerm : Perm (Fin n))) j i, hinv, permRank_revPerm_mul,
    permRank_inv s j (n - i)]

end Equiv.Perm
