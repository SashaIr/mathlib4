/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.Greene.Theorem
import Mathlib.Combinatorics.Young.Word.Standardization

/-!
# The inverse of a standard word

A Lean 4 port of the inverse `invstd` of a standard word of `theories/LRrule/stdplact.v`
from [Coq-Combi](https://github.com/math-comp/Coq-Combi).

A standard word `w` of length `n` is a permutation of `0, …, n-1`, written as the list of
its values.  Its *inverse* is the standard word listing, for each letter `i`, the position
of `i` in `w`.

## Main definitions

* `List.invStd w` : the inverse of the standard word `w` (Coq `invstd`).
* `List.IsInvSeq u v` : `u` and `v` are inverse to each other (Coq `invseq`).

## Main results

* `List.isStd_invStd` : the inverse of a standard word is a standard word
  (Coq `invstd_is_std`).
* `List.invStd_invStd` : inverting is an involution (Coq `invstdK`).
* `List.isInvSeq_invStd`, `List.IsInvSeq.symm` : `w` and `invStd w` are inverse sequences,
  and the relation is symmetric.
* `List.greeneRow_invStd` : a word and its inverse have the same Greene row invariants.
* `List.shape_RS_invStd` : consequently, a standard word and its inverse have Robinson–
  Schensted tableaux of the same shape.
-/

namespace List

open List

variable {w : List ℕ}

/-! ### The inverse of a standard word -/

/-- The inverse of the standard word `w`: its `i`-th letter is the position of `i` in `w`
(Coq `invstd`). -/
def invStd (w : List ℕ) : List ℕ := (range w.length).map fun i => w.idxOf i

@[simp] lemma length_invStd (w : List ℕ) : (invStd w).length = w.length := by
  simp [invStd]

@[simp] lemma getElem_invStd (w : List ℕ) {i : ℕ} (hi : i < (invStd w).length) :
    (invStd w)[i] = w.idxOf i := by
  simp only [invStd, getElem_map, getElem_range]

lemma IsStd.mem_of_lt (hw : IsStd w) {i : ℕ} (hi : i < w.length) : i ∈ w :=
  hw.mem_iff.2 (mem_range.2 hi)

lemma IsStd.nodup' (hw : IsStd w) : w.Nodup := hw.nodup_iff.2 nodup_range

lemma IsStd.idxOf_lt (hw : IsStd w) {i : ℕ} (hi : i < w.length) : w.idxOf i < w.length :=
  idxOf_lt_length_iff.2 (hw.mem_of_lt hi)

lemma IsStd.getElem_idxOf (hw : IsStd w) {i : ℕ} (hi : i < w.length) :
    w[w.idxOf i]'(hw.idxOf_lt hi) = i :=
  List.getElem_idxOf _

lemma IsStd.idxOf_getElem (hw : IsStd w) {j : ℕ} (hj : j < w.length) : w.idxOf w[j] = j :=
  Nodup.idxOf_getElem hw.nodup' j hj

lemma IsStd.getElem_lt (hw : IsStd w) {j : ℕ} (hj : j < w.length) : w[j] < w.length := by
  have := hw.mem_iff (a := w[j])
  exact mem_range.1 (this.1 (getElem_mem hj))

/-- **The inverse of a standard word is standard** (Coq `invstd_is_std`). -/
theorem isStd_invStd (hw : IsStd w) : IsStd (invStd w) := by
  have hnodup : (invStd w).Nodup := by
    refine (nodup_map_iff_inj_on nodup_range).2 fun i hi j hj hij => ?_
    have hi' : i < w.length := mem_range.1 hi
    have hj' : j < w.length := mem_range.1 hj
    calc i = w[w.idxOf i]'(hw.idxOf_lt hi') := (hw.getElem_idxOf hi').symm
      _ = w[w.idxOf j]'(hw.idxOf_lt hj') := by simp only [hij]
      _ = j := hw.getElem_idxOf hj'
  have hsub : invStd w ⊆ range (invStd w).length := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_map.1 hx
    exact mem_range.2 (by simpa using hw.idxOf_lt (mem_range.1 hi))
  exact (hnodup.subperm hsub).perm_of_length_le (by simp)

/-- **Inverting a standard word is an involution** (Coq `invstdK`). -/
theorem invStd_invStd (hw : IsStd w) : invStd (invStd w) = w := by
  have hlen : (invStd (invStd w)).length = w.length := by simp
  refine List.ext_getElem hlen fun i hi hi' => ?_
  have hiw : i < w.length := by simpa using hi'
  have hkey : (invStd w)[w[i]]'(by simpa using hw.getElem_lt hiw) = i := by
    rw [getElem_invStd]
    exact hw.idxOf_getElem hiw
  rw [getElem_invStd]
  calc (invStd w).idxOf i
      = (invStd w).idxOf ((invStd w)[w[i]]'(by simpa using hw.getElem_lt hiw)) := by rw [hkey]
    _ = w[i] := Nodup.idxOf_getElem (isStd_invStd hw).nodup' _ _

/-! ### Inverse sequences -/

/-- Two words are *inverse sequences* when they have the same length and applying one after
the other is the identity (Coq `invseq`). -/
def IsInvSeq (u v : List ℕ) : Prop :=
  u.length = v.length ∧ ∀ i < u.length, u.getD i 0 < v.length ∧ v.getD (u.getD i 0) 0 = i

lemma getD_invStd {i : ℕ} (hi : i < w.length) : (invStd w).getD i 0 = w.idxOf i := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), getElem_invStd]

lemma IsStd.getD_lt' (hw : IsStd w) {i : ℕ} (hi : i < w.length) : w.getD i 0 < w.length := by
  rw [List.getD_eq_getElem _ _ hi]
  exact hw.getElem_lt hi

lemma IsStd.getD_idxOf (hw : IsStd w) {i : ℕ} (hi : i < w.length) :
    w.getD (w.idxOf i) 0 = i := by
  rw [List.getD_eq_getElem _ _ (hw.idxOf_lt hi)]
  exact hw.getElem_idxOf hi

lemma IsStd.idxOf_getD (hw : IsStd w) {j : ℕ} (hj : j < w.length) :
    w.idxOf (w.getD j 0) = j := by
  rw [List.getD_eq_getElem _ _ hj]
  exact hw.idxOf_getElem hj

/-- A standard word and its inverse are inverse sequences. -/
lemma isInvSeq_invStd (hw : IsStd w) : IsInvSeq w (invStd w) := by
  refine ⟨by simp, fun i hi => ?_⟩
  have hlt : w.getD i 0 < (invStd w).length := by simpa using hw.getD_lt' hi
  exact ⟨hlt, by rw [getD_invStd (by simpa using hlt), hw.idxOf_getD hi]⟩

/-- The inverse of a standard word and the word itself are inverse sequences. -/
lemma isInvSeq_invStd_left (hw : IsStd w) : IsInvSeq (invStd w) w := by
  refine ⟨by simp, fun j hj => ?_⟩
  have hjw : j < w.length := by simpa using hj
  rw [getD_invStd hjw]
  exact ⟨hw.idxOf_lt hjw, hw.getD_idxOf hjw⟩

/-! ### Greene invariants -/

/-- A colouring of the positions of `w`, transported to the inverse word: the position `j`
of the inverse word corresponds to the position of the letter `j` in `w`. -/
private def transportCol (w : List ℕ) (c : ℕ → Option ℕ) : ℕ → Option ℕ := fun j =>
  if j < w.length then c (w.idxOf j) else none

private lemma isGreeneCol_transportCol (hw : IsStd w) {k : ℕ} {c : ℕ → Option ℕ}
    (hc : IsGreeneCol w k c) : IsGreeneCol (invStd w) k (transportCol w c) := by
  refine ⟨fun j x hx => ?_, fun j1 j2 x hj12 hj2 h1 h2 => ?_⟩
  · rw [transportCol] at hx
    split at hx
    · exact hc.lt_of_colour hx
    · exact absurd hx (by simp)
  · have hj2w : j2 < w.length := by simpa using hj2
    have hj1w : j1 < w.length := hj12.trans hj2w
    rw [transportCol, ite_eq_left hj1w] at h1
    rw [transportCol, ite_eq_left hj2w] at h2
    simp only [getElem_invStd]
    have hi1 : w.idxOf j1 < w.length := hw.idxOf_lt hj1w
    have hi2 : w.idxOf j2 < w.length := hw.idxOf_lt hj2w
    by_contra hcon
    push Not at hcon
    have hle := hc.le_of_colour hcon hi1 h2 h1
    rw [hw.getElem_idxOf hj2w, hw.getElem_idxOf hj1w] at hle
    omega

private lemma greeneSize_transportCol (hw : IsStd w) (c : ℕ → Option ℕ) :
    greeneSize (invStd w) (transportCol w c) = greeneSize w c := by
  classical
  refine Finset.card_nbij' (fun j => w.idxOf j) (fun i => w.getD i 0) ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range, length_invStd] at hj ⊢
    obtain ⟨hjr, hjs⟩ := hj
    rw [transportCol, ite_eq_left hjr] at hjs
    exact ⟨hw.idxOf_lt hjr, hjs⟩
  · intro i hi
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range, length_invStd] at hi ⊢
    obtain ⟨hir, his⟩ := hi
    have hlt : w.getD i 0 < w.length := hw.getD_lt' hir
    refine ⟨hlt, ?_⟩
    rw [transportCol, ite_eq_left hlt, hw.idxOf_getD hir]
    exact his
  · intro j hj
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range, length_invStd] at hj
    exact hw.getD_idxOf hj.1
  · intro i hi
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hi
    exact hw.idxOf_getD hi.1

private lemma greeneRow_le_greeneRow_invStd (hw : IsStd w) (k : ℕ) :
    greeneRow w k ≤ greeneRow (invStd w) k := by
  obtain ⟨c, hc, hsize⟩ := exists_greeneCol w k
  rw [← hsize, ← greeneSize_transportCol hw c]
  exact le_greeneRow (isGreeneCol_transportCol hw hc)

/-- **A standard word and its inverse have the same Greene row invariants.** -/
theorem greeneRow_invStd (hw : IsStd w) (k : ℕ) : greeneRow (invStd w) k = greeneRow w k := by
  refine le_antisymm ?_ (greeneRow_le_greeneRow_invStd hw k)
  have hle := greeneRow_le_greeneRow_invStd (isStd_invStd hw) k
  rwa [invStd_invStd hw] at hle

/-- **A standard word and its inverse have Robinson–Schensted tableaux of the same shape.**
This is the shape part of Coq `RSinvstdE`. -/
theorem shape_RS_invStd (hw : IsStd w) : shape (RS (invStd w)) = shape (RS w) := by
  refine sum_take_inj (isPart_shape (isTableau_RS _)) (isPart_shape (isTableau_RS _)) fun k => ?_
  rw [← greeneRow_eq_sum_take_shape, ← greeneRow_eq_sum_take_shape, greeneRow_invStd hw]

end List
