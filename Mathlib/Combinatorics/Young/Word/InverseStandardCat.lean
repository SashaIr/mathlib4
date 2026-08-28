/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.Word.InverseStandard
import Mathlib.Combinatorics.Young.Word.ShiftedShuffle

/-!
# The inverse standardization of a concatenation

A Lean 4 port of `invstd_catgtn`, `invstd_catleq` and `invstd_cat_in_shsh` in
`theories/LRrule/shuffle.v` of [Coq-Combi](https://github.com/math-comp/Coq-Combi).

The inverse of the standardization of a word `w` lists the positions of `w` sorted by the
standardization order (by increasing letter, ties broken by increasing position).  For a
concatenation `u ++ v`, the positions coming from `u` are those `< |u|`, and reading them
off in order gives the inverse standardization of `u`; the positions coming from `v` are the
ones `≥ |u|`, and shifting them down by `|u|` gives the inverse standardization of `v`.
Consequently `invStd (std (u ++ v))` is a shifted shuffle of `invStd (std u)` and
`invStd (std v)`; this is essentially the product rule of the Hopf algebra `FQSym`.

## Main definitions

* `List.stdBefore w` : the relation "position `i` carries a smaller standardized letter
  than position `j`" on the positions of `w`.

## Main results

* `List.filter_lt_invStd_std_append` : the positions `< |u|` of `invStd (std (u ++ v))`
  spell `invStd (std u)` (Coq `invstd_catgtn`).
* `List.sfilterleq_invStd_std_append` : the positions `≥ |u|` of `invStd (std (u ++ v))`,
  shifted down, spell `invStd (std v)` (Coq `invstd_catleq`).
* `List.filter_lt_invStd_std_take` and `List.sfilterleq_invStd_std_drop` : the same
  statements for the prefix and the suffix of a word (Coq `sfiltergtn_invstd` and
  `sfilterleq_invstd`).
* `List.invStd_std_append_mem_shsh` : `invStd (std (u ++ v))` is a shifted shuffle of
  `invStd (std u)` and `invStd (std v)` (Coq `invstd_cat_in_shsh`).
-/

namespace List

variable {T : Type*} [LinearOrder T] {u v : List T}

/-! ### The standardization order on positions -/

/-- The position `i` comes before the position `j` in the word `w` when the standardized
word carries a smaller letter at `i` than at `j`. -/
def stdBefore (w : List T) (i j : ℕ) : Prop := (std w).getD i 0 < (std w).getD j 0

lemma stdBefore_asymm {w : List T} {i j : ℕ} (h : stdBefore w i j) : ¬ stdBefore w j i :=
  fun h' => absurd (h.trans h') (lt_irrefl _)

/-- Two positions comparable in both directions are equal: vacuously, since `stdBefore` is
asymmetric. -/
lemma eq_of_stdBefore_of_stdBefore {w : List T} {i j : ℕ} (h : stdBefore w i j)
    (h' : stdBefore w j i) : i = j :=
  absurd h' (stdBefore_asymm h)

/-- The inverse standardization of a word lists its positions in the standardization
order. -/
theorem sorted_invStd_std (w : List T) : Pairwise (stdBefore w) (invStd (std w)) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hstd : IsStd (std w) := std_isStd w
  have hi' : i < (std w).length := by simpa using hi
  have hj' : j < (std w).length := by simpa using hj
  rw [getElem_invStd, getElem_invStd]
  simpa only [stdBefore, hstd.getD_idxOf hi', hstd.getD_idxOf hj'] using hij

/-- On the positions of `u`, the standardization order of `u ++ v` is that of `u`. -/
lemma stdBefore_append_left {i j : ℕ} (hi : i < u.length) (hj : j < u.length) :
    stdBefore (u ++ v) i j ↔ stdBefore u i j := by
  have hi' : i < (u ++ v).length := by simp; omega
  have hj' : j < (u ++ v).length := by simp; omega
  rw [stdBefore, stdBefore, List.getD_eq_getElem _ _ (by simpa using hi'),
    List.getD_eq_getElem _ _ (by simpa using hj'), List.getD_eq_getElem _ _ (by simpa using hi),
    List.getD_eq_getElem _ _ (by simpa using hj), getElem_std_lt_getElem_std_iff _ hi' hj',
    getElem_std_lt_getElem_std_iff _ hi hj, List.getElem_append_left hi,
    List.getElem_append_left hj]

/-- On the positions of `v`, shifted by `|u|`, the standardization order of `u ++ v` is that
of `v`. -/
lemma stdBefore_append_right {i j : ℕ} (hi : i < v.length) (hj : j < v.length) :
    stdBefore (u ++ v) (u.length + i) (u.length + j) ↔ stdBefore v i j := by
  have hi' : u.length + i < (u ++ v).length := by simp; omega
  have hj' : u.length + j < (u ++ v).length := by simp; omega
  rw [stdBefore, stdBefore, List.getD_eq_getElem _ _ (by simpa using hi'),
    List.getD_eq_getElem _ _ (by simpa using hj'), List.getD_eq_getElem _ _ (by simpa using hi),
    List.getD_eq_getElem _ _ (by simpa using hj), getElem_std_lt_getElem_std_iff _ hi' hj',
    getElem_std_lt_getElem_std_iff _ hi hj]
  rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left, Nat.add_lt_add_iff_left]

/-! ### Splitting the inverse standardization of a concatenation -/

private lemma isStd_invStd_std (w : List T) : IsStd (invStd (std w)) :=
  isStd_invStd (std_isStd w)

/-- **The positions of `u` inside `invStd (std (u ++ v))`** (Coq `invstd_catgtn`): keeping
the letters `< |u|` of the inverse standardization of `u ++ v` gives the inverse
standardization of `u`. -/
theorem filter_lt_invStd_std_append (u v : List T) :
    (invStd (std (u ++ v))).filter (fun x => decide (x < u.length)) = invStd (std u) := by
  set A := invStd (std (u ++ v)) with hA
  have hstdA : IsStd A := isStd_invStd_std _
  have hlenA : A.length = u.length + v.length := by simp [hA]
  set L := A.filter (fun x => decide (x < u.length)) with hL
  have hsubL : L ⊆ range u.length := by
    intro x hx
    rw [hL, List.mem_filter] at hx
    exact mem_range.2 (by simpa using hx.2)
  have hsupL : range u.length ⊆ L := by
    intro x hx
    have hxu : x < u.length := mem_range.1 hx
    rw [hL, List.mem_filter]
    exact ⟨hstdA.mem_of_lt (by omega), by simpa using hxu⟩
  have hnodupL : L.Nodup := (List.filter_sublist).nodup hstdA.nodup'
  have hpermL : L.Perm (range u.length) :=
    (List.subperm_of_subset hnodupL hsubL).antisymm
      (List.subperm_of_subset nodup_range hsupL)
  have hperm : L.Perm (invStd (std u)) :=
    hpermL.trans ((isStd_invStd_std u).trans (by simp)).symm
  refine List.Perm.eq_of_pairwise (le := stdBefore u)
    (fun a b _ _ h h' => eq_of_stdBefore_of_stdBefore h h') ?_ (sorted_invStd_std u) hperm
  have hpair : Pairwise (stdBefore (u ++ v)) L :=
    List.Pairwise.sublist List.filter_sublist (sorted_invStd_std (u ++ v))
  refine hpair.imp_of_mem fun {a b} ha hb h => ?_
  exact (stdBefore_append_left (mem_range.1 (hsubL ha)) (mem_range.1 (hsubL hb))).1 h

/-- **The positions of `v` inside `invStd (std (u ++ v))`** (Coq `invstd_catleq`): keeping
the letters `≥ |u|` of the inverse standardization of `u ++ v` and shifting them down gives
the inverse standardization of `v`. -/
theorem sfilterleq_invStd_std_append (u v : List T) :
    sfilterleq u.length (invStd (std (u ++ v))) = invStd (std v) := by
  set A := invStd (std (u ++ v)) with hA
  have hstdA : IsStd A := isStd_invStd_std _
  have hlenA : A.length = u.length + v.length := by simp [hA]
  set F := A.filter (fun x => decide (u.length ≤ x)) with hF
  have hmemF : ∀ x ∈ F, u.length ≤ x ∧ x < u.length + v.length := by
    intro x hx
    rw [hF, List.mem_filter] at hx
    refine ⟨by simpa using hx.2, ?_⟩
    have := hstdA.mem_iff.1 hx.1
    rw [hlenA] at this
    exact mem_range.1 this
  have hsub : sfilterleq u.length A ⊆ range v.length := by
    intro x hx
    rw [sfilterleq, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨h1, h2⟩ := hmemF y hy
    exact mem_range.2 (by omega)
  have hsup : range v.length ⊆ sfilterleq u.length A := by
    intro x hx
    have hxv : x < v.length := mem_range.1 hx
    rw [sfilterleq, List.mem_map]
    refine ⟨u.length + x, ?_, by omega⟩
    rw [hF] at *
    rw [List.mem_filter]
    exact ⟨hstdA.mem_of_lt (by omega), by simp⟩
  have hnodupF : F.Nodup := (List.filter_sublist).nodup hstdA.nodup'
  have hnodup : (sfilterleq u.length A).Nodup := by
    refine hnodupF.map_on ?_
    intro x hx y hy hxy
    obtain ⟨h1, -⟩ := hmemF x hx
    obtain ⟨h2, -⟩ := hmemF y hy
    omega
  have hperm : (sfilterleq u.length A).Perm (invStd (std v)) :=
    ((List.subperm_of_subset hnodup hsub).antisymm
      (List.subperm_of_subset nodup_range hsup)).trans
      ((isStd_invStd_std v).trans (by simp)).symm
  refine List.Perm.eq_of_pairwise (le := stdBefore v)
    (fun a b _ _ h h' => eq_of_stdBefore_of_stdBefore h h') ?_ (sorted_invStd_std v) hperm
  have hpairF : Pairwise (stdBefore (u ++ v)) F :=
    List.Pairwise.sublist List.filter_sublist (sorted_invStd_std (u ++ v))
  rw [sfilterleq, List.pairwise_map]
  refine hpairF.imp_of_mem fun {a b} ha hb h => ?_
  obtain ⟨ha1, ha2⟩ := hmemF a ha
  obtain ⟨hb1, hb2⟩ := hmemF b hb
  have hrw : ∀ {x : ℕ}, u.length ≤ x → x = u.length + (x - u.length) := by intro x hx; omega
  rw [hrw ha1, hrw hb1] at h
  exact (stdBefore_append_right (by omega) (by omega)).1 h

/-- Keeping the letters `< n` of the inverse standardization of `w` gives the inverse
standardization of the prefix of length `n` (Coq `sfiltergtn_invstd`). -/
theorem filter_lt_invStd_std_take {w : List T} {n : ℕ} (hn : n ≤ w.length) :
    (invStd (std w)).filter (fun x => decide (x < n)) = invStd (std (w.take n)) := by
  have hlen : (w.take n).length = n := by simp; omega
  have := filter_lt_invStd_std_append (w.take n) (w.drop n)
  rwa [List.take_append_drop, hlen] at this

/-- Keeping the letters `≥ n` of the inverse standardization of `w` and shifting them down
gives the inverse standardization of the suffix after `n` (Coq `sfilterleq_invstd`). -/
theorem sfilterleq_invStd_std_drop {w : List T} {n : ℕ} (hn : n ≤ w.length) :
    sfilterleq n (invStd (std w)) = invStd (std (w.drop n)) := by
  have hlen : (w.take n).length = n := by simp; omega
  have := sfilterleq_invStd_std_append (w.take n) (w.drop n)
  rwa [List.take_append_drop, hlen] at this

/-- **The inverse standardization of a concatenation is a shifted shuffle** (Coq
`invstd_cat_in_shsh`), essentially the product rule of `FQSym`. -/
theorem invStd_std_append_mem_shsh (u v : List T) :
    invStd (std (u ++ v)) ∈ shsh (invStd (std u)) (invStd (std v)) := by
  have hu : ∀ x ∈ invStd (std u), x < (invStd (std u)).length :=
    fun x hx => mem_range.1 ((isStd_invStd_std u).mem_iff.1 hx)
  rw [mem_shsh hu]
  simp only [length_invStd, length_std]
  exact ⟨filter_lt_invStd_std_append u v, sfilterleq_invStd_std_append u v⟩

end List
