/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.RobinsonSchensted.Bijection
import Mathlib.Combinatorics.Young.Tableau.Restrict

/-!
# A standard tableau is determined by the shapes of its restrictions

A standard tableau contains each of the letters `0, …, n - 1` exactly once, so the shape of
the tableau of its letters `< k` grows by exactly one box at each step, the box containing
the letter `k`.  Consequently two standard tableaux whose restrictions have the same
shapes are equal: this is the description of a standard tableau as a chain of shapes.

## Main results

* `List.mem_getD_iff_of_shape_dropMax_eq` : if the restrictions of two standard tableaux
  have the same shapes, then the two tableaux have the same letters in each row.
* `List.eq_of_shape_dropMax_eq` : **two standard tableaux whose restrictions have the same
  shapes are equal**.
-/

namespace List

open List

/-- A tableau all of whose letters are `< N` is its own restriction. -/
lemma dropMax_of_forall_lt {N : ℕ} {P : List (List ℕ)} (hP : IsTableau P)
    (h : ∀ x ∈ P.flatten, x < N) : dropMax N P = P := by
  induction P with
  | nil => rfl
  | cons r P ih =>
    have hr : ltFilter N r = r := by
      rw [ltFilter, List.filter_eq_self]
      intro x hx
      simpa using h x (by simp [hx])
    rw [dropMax_cons, hr, ite_eq_right hP.1, ih hP.2.2.2 fun x hx => h x (by simp [hx])]

/-- Restricting to the letters `< m + 1` rather than `< m` adds the letter `m` when the
row contains it. -/
lemma length_ltFilter_succ (m : ℕ) {r : List ℕ} (hr : r.Nodup) :
    (ltFilter (m + 1) r).length = (ltFilter m r).length + (if m ∈ r then 1 else 0) := by
  induction r with
  | nil => simp
  | cons a r ih =>
    have hnd : r.Nodup := hr.of_cons
    have ha : a ∉ r := (List.nodup_cons.1 hr).1
    rcases lt_trichotomy a m with h | rfl | h
    · have hmem : (m ∈ a :: r) ↔ (m ∈ r) :=
        ⟨fun hc => (List.mem_cons.1 hc).resolve_left (by omega),
          fun hc => List.mem_cons.2 (Or.inr hc)⟩
      rw [ltFilter_cons_of_lt _ (by omega : a < m + 1), ltFilter_cons_of_lt _ h]
      simp only [List.length_cons, ih hnd, hmem]
      omega
    · rw [ltFilter_cons_of_lt _ (by omega : a < a + 1), ltFilter_cons_of_ge _ (by omega),
        List.length_cons, ih hnd, ite_eq_left (List.mem_cons_self ..), ite_eq_right ha]
    · have hmem : (m ∈ a :: r) ↔ (m ∈ r) :=
        ⟨fun hc => (List.mem_cons.1 hc).resolve_left (by omega),
          fun hc => List.mem_cons.2 (Or.inr hc)⟩
      rw [ltFilter_cons_of_ge _ (by omega), ltFilter_cons_of_ge _ (by omega)]
      simp only [ih hnd, hmem]

/-- The rows of a standard tableau have no repeated letter. -/
lemma nodup_getD_of_isStdTab {P : List (List ℕ)} (hP : IsStdTab P) (i : ℕ) :
    (P.getD i []).Nodup := by
  rcases Nat.lt_or_ge i P.length with hi | hi
  · have hword : (toWord P).Nodup := hP.2.nodup_iff.2 List.nodup_range
    rw [toWord, List.nodup_flatten] at hword
    refine hword.1 _ ?_
    rw [List.getD_eq_getElem _ _ hi, List.mem_reverse]
    exact List.getElem_mem hi
  · rw [List.getD_eq_default _ _ hi]
    exact List.nodup_nil

/-- The letters of a standard tableau are smaller than its size. -/
lemma lt_sizeTab_of_mem_flatten {P : List (List ℕ)} (hP : IsStdTab P) {x : ℕ}
    (hx : x ∈ P.flatten) : x < sizeTab P := by
  obtain ⟨r, hr, hxr⟩ := List.mem_flatten.1 hx
  exact (mem_toWord_iff_of_isStdTab hP x).1 (mem_toWord_iff.2 ⟨r, hr, hxr⟩)

/-- In a standard tableau, the shapes of the restrictions determine, for each letter and
each row, whether that row contains that letter. -/
lemma mem_getD_iff_of_shape_dropMax_eq {P Q : List (List ℕ)} (hP : IsStdTab P)
    (hQ : IsStdTab Q) (h : ∀ k, shape (dropMax k P) = shape (dropMax k Q)) (i m : ℕ) :
    m ∈ P.getD i [] ↔ m ∈ Q.getD i [] := by
  have key : ∀ k, (ltFilter k (P.getD i [])).length = (ltFilter k (Q.getD i [])).length := by
    intro k
    have hk := congrArg (fun s => s.getD i 0) (h k)
    simpa only [getD_shape_dropMax hP.1, getD_shape_dropMax hQ.1] using hk
  have h1 := length_ltFilter_succ m (nodup_getD_of_isStdTab hP i)
  have h2 := length_ltFilter_succ m (nodup_getD_of_isStdTab hQ i)
  have e1 := key m
  have e2 := key (m + 1)
  refine ⟨fun hp => ?_, fun hq => ?_⟩
  · by_contra hq
    rw [ite_eq_left hp] at h1
    rw [ite_eq_right hq] at h2
    omega
  · by_contra hp
    rw [ite_eq_right hp] at h1
    rw [ite_eq_left hq] at h2
    omega

/-- **Two standard tableaux whose restrictions to the letters `< k` have the same shape
for every `k` are equal.** -/
theorem eq_of_shape_dropMax_eq {P Q : List (List ℕ)} (hP : IsStdTab P) (hQ : IsStdTab Q)
    (h : ∀ k, shape (dropMax k P) = shape (dropMax k Q)) : P = Q := by
  set K := max (sizeTab P) (sizeTab Q) with hK
  have hshape : shape P = shape Q := by
    have hk := h K
    rwa [dropMax_of_forall_lt hP.1 fun x hx =>
        lt_of_lt_of_le (lt_sizeTab_of_mem_flatten hP hx) (le_max_left _ _),
      dropMax_of_forall_lt hQ.1 fun x hx =>
        lt_of_lt_of_le (lt_sizeTab_of_mem_flatten hQ hx) (le_max_right _ _)] at hk
  have hlen : P.length = Q.length := by
    have := congrArg List.length hshape
    simpa using this
  have hsize : sizeTab P = sizeTab Q := by rw [sizeTab, sizeTab, hshape]
  have hmem := mem_getD_iff_of_shape_dropMax_eq hP hQ h
  have hrows : rowsOf P = rowsOf Q := by
    rw [rowsOf, rowsOf, hsize]
    refine List.map_congr_left fun m hm => ?_
    have hm' : m < sizeTab P := by
      rw [hsize]
      simpa using hm
    have hex : ∃ r ∈ P, m ∈ r :=
      mem_toWord_iff.1 ((mem_toWord_iff_of_isStdTab hP m).2 hm')
    obtain ⟨hlt, hmemP, hbelow⟩ := rowIdx_spec hex
    exact (rowIdx_eq_of (by omega) ((hmem _ m).1 hmemP)
      fun j hj hc => hbelow j hj ((hmem j m).2 hc)).symm
  rw [← recTab_rowsOf hP, ← recTab_rowsOf hQ, hrows]

end List
