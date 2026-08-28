/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.Plactic.Standardization
import Mathlib.Combinatorics.Young.Tableau.Restrict
import Mathlib.Combinatorics.Young.Word.InverseStandard

/-!
# Restricting the inverse of a standard word

The inverse `List.invStd w` of a standard word lists, for each letter of `w` in increasing
order, its position in `w`.  Keeping only the letters `< k` of the inverse therefore means
keeping only the positions in the prefix of length `k` of `w`, so that the restricted word
is the inverse of the standardisation of that prefix.

## Main results

* `List.std_of_isStd` : a standard word is its own standardisation.
* `List.ltFilter_invStd` : `ltFilter k (invStd w) = invStd (std (w.take k))`.
-/

namespace List

open List

/-! ### Auxiliary results on lists -/

/-- Filtering the image of a list is the image of the filtered list. -/
lemma filter_map_eq_map_filter {α β : Type*} (f : α → β) (q : β → Bool) (l : List α) :
    (l.map f).filter q = (l.filter fun i => q (f i)).map f := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases h : q (f a) <;> simp [h, ih]

/-- The index of the last element of a list in which it occurs only once. -/
lemma idxOf_append_singleton {α : Type*} [DecidableEq α] {L : List α} {v : α} (h : v ∉ L) :
    (L ++ [v]).idxOf v = L.length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ha : a ≠ v := fun he => h (by simp [he])
    have hL : v ∉ L := fun hc => h (by simp [hc])
    simp [ha, ih hL]

/-- In the list of the elements `< n` satisfying a predicate, the index of `v` is the
number of elements `< v` satisfying it. -/
lemma idxOf_filter_range {n : ℕ} (P : ℕ → Bool) {v : ℕ} (hv : v < n) (hP : P v = true) :
    ((List.range n).filter P).idxOf v = ((List.range v).filter P).length := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.filter_append]
    rcases Nat.lt_or_ge v n with h | h
    · rw [List.idxOf_append_of_mem (by simp [List.mem_filter, h, hP])]
      exact ih h
    · obtain rfl : v = n := by omega
      rw [List.filter_cons_of_pos hP, List.filter_nil]
      exact idxOf_append_singleton (by simp)

/-- The index in the image of a list of the image of one of its elements, when no other
element has the same image. -/
lemma idxOf_map_eq {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β} {v : α} :
    ∀ {S : List α}, (∀ x ∈ S, f x = f v → x = v) → (S.map f).idxOf (f v) = S.idxOf v
  | [], _ => by simp
  | a :: S, h => by
    by_cases ha : a = v
    · subst ha
      simp
    · have hfa : f a ≠ f v := fun hc => ha (h a (by simp) hc)
      rw [List.map_cons, List.idxOf_cons_ne _ hfa, List.idxOf_cons_ne _ ha,
        idxOf_map_eq fun x hx => h x (by simp [hx])]

/-! ### A standard word is its own standardisation -/

/-- A standard word is its own standardisation. -/
theorem std_of_isStd {w : List ℕ} (hw : IsStd w) : std w = w := by
  refine eq_of_isStd_of_lt_iff (std_isStd w) hw (by simp) fun i j hi hj => ?_
  have hi' : i < w.length := by simpa using hi
  have hj' : j < w.length := by simpa using hj
  rw [getD_std_lt_getD_std_iff w 0 hi' hj']
  refine or_iff_left fun h => ?_
  have hne : i ≠ j := fun he => absurd (he ▸ h.2) (lt_irrefl _)
  rw [List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hj'] at h
  refine hne ?_
  calc i = w.idxOf w[i] := (hw.idxOf_getElem hi').symm
    _ = w.idxOf w[j] := by rw [h.1]
    _ = j := hw.idxOf_getElem hj'

/-! ### Restricting the inverse -/

variable {w : List ℕ} {k : ℕ}

/-- The positions of the letters of `w` occurring in the prefix of length `k`, in
increasing order of the letter. -/
private def smallPos (w : List ℕ) (k : ℕ) : List ℕ :=
  (List.range w.length).filter fun i => decide (w.idxOf i < k)

private lemma ltFilter_invStd_eq_map (w : List ℕ) (k : ℕ) :
    ltFilter k (invStd w) = (smallPos w k).map fun i => w.idxOf i := by
  rw [invStd, ltFilter, filter_map_eq_map_filter, smallPos]

private lemma mem_ltFilter_invStd (hw : IsStd w) (x : ℕ) :
    x ∈ ltFilter k (invStd w) ↔ x < min k w.length := by
  rw [mem_ltFilter, (isStd_invStd hw).mem_iff]
  simp only [List.mem_range, length_invStd, lt_min_iff]
  tauto

private lemma perm_ltFilter_invStd (hw : IsStd w) :
    (ltFilter k (invStd w)).Perm (List.range (min k w.length)) := by
  refine (List.perm_ext_iff_of_nodup ?_ List.nodup_range).2 fun x => ?_
  · exact ((isStd_invStd hw).nodup').filter _
  · rw [mem_ltFilter_invStd hw, List.mem_range]

private lemma length_ltFilter_invStd (hw : IsStd w) :
    (ltFilter k (invStd w)).length = min k w.length :=
  (perm_ltFilter_invStd (k := k) hw).length_eq.trans (by simp)

private lemma isStd_ltFilter_invStd (hw : IsStd w) : IsStd (ltFilter k (invStd w)) := by
  rw [IsStd, length_ltFilter_invStd hw]
  exact perm_ltFilter_invStd hw

/-- The index of a position in the restricted inverse counts the smaller letters of the
prefix. -/
private lemma idxOf_ltFilter_invStd (hw : IsStd w) {j : ℕ} (hj : j < min k w.length) :
    (ltFilter k (invStd w)).idxOf j
      = ((List.range (w.getD j 0)).filter fun i => decide (w.idxOf i < k)).length := by
  have hjw : j < w.length := lt_of_lt_of_le hj (min_le_right _ _)
  have hjk : j < k := lt_of_lt_of_le hj (min_le_left _ _)
  set v := w.getD j 0 with hv
  have hvn : v < w.length := hw.getD_lt' hjw
  have hidx : w.idxOf v = j := hw.idxOf_getD hjw
  have hinj : ∀ x ∈ smallPos w k, w.idxOf x = w.idxOf v → x = v := by
    intro x hx hxv
    have hxn : x < w.length := by
      have := List.mem_filter.1 hx
      simpa using this.1
    calc x = w.getD (w.idxOf x) 0 := (hw.getD_idxOf hxn).symm
      _ = w.getD (w.idxOf v) 0 := by rw [hxv]
      _ = v := hw.getD_idxOf hvn
  rw [ltFilter_invStd_eq_map, ← hidx, idxOf_map_eq hinj, smallPos,
    idxOf_filter_range _ hvn (by simpa [hidx] using hjk)]

/-- The standardisation of the prefix counts the smaller letters of the prefix. -/
private lemma getElem_std_take (hw : IsStd w) {j : ℕ} (hj : j < min k w.length) :
    (std (w.take k))[j]'(by simpa using hj)
      = ((List.range (w.getD j 0)).filter fun i => decide (w.idxOf i < k)).length := by
  classical
  have hjw : j < w.length := lt_of_lt_of_le hj (min_le_right _ _)
  have hjk : j < k := lt_of_lt_of_le hj (min_le_left _ _)
  have hlen : (w.take k).length = min k w.length := by simp
  have hAget : ∀ (q : ℕ) (hq : q < (w.take k).length), (w.take k)[q] = w.getD q 0 := by
    intro q hq
    have hq2 : q < w.length := by
      rw [hlen] at hq
      omega
    rw [List.getElem_take, List.getD_eq_getElem _ _ hq2]
  have hjA : j < (w.take k).length := by rw [hlen]; exact hj
  set v := w.getD j 0 with hv
  have hvn : v < w.length := hw.getD_lt' hjw
  have hcount : ((List.range v).filter fun i => decide (w.idxOf i < k)).length
      = ((Finset.range v).filter fun i => w.idxOf i < k).card := rfl
  rw [getElem_std, stdRank, hcount]
  refine Finset.card_bij' (i := fun q _ => (w.take k)[q.1]'q.2)
    (j := fun i hi => (⟨w.idxOf i, by
      have h1 := Finset.mem_filter.1 hi
      have hiv : i < v := Finset.mem_range.1 h1.1
      have hin : i < w.length := hiv.trans hvn
      rw [hlen]
      exact lt_min h1.2 (hw.idxOf_lt hin)⟩ : Fin (w.take k).length)) ?_ ?_ ?_ ?_
  · rintro ⟨q, hq⟩ hmem
    dsimp only
    have hq' : q < min k w.length := by rwa [hlen] at hq
    have hqn : q < w.length := lt_of_lt_of_le hq' (min_le_right _ _)
    have hstd : stdLt (w.take k) ⟨q, hq⟩ ⟨j, hjA⟩ := (Finset.mem_filter.1 hmem).2
    have hAq : (w.take k)[q]'hq = w.getD q 0 := hAget q hq
    have hAj : (w.take k)[j]'hjA = v := hAget j hjA
    have hlt : w.getD q 0 < v := by
      rcases hstd with h | ⟨h, hqj⟩
      · rwa [hAq, hAj] at h
      · rw [hAq, hAj] at h
        have hqj' : q < j := hqj
        have hqeq : q = j := by
          calc q = w.idxOf (w.getD q 0) := (hw.idxOf_getD hqn).symm
            _ = w.idxOf v := by rw [h]
            _ = j := hw.idxOf_getD hjw
        omega
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (by rw [hAq]; exact hlt), ?_⟩
    rw [hAq, hw.idxOf_getD hqn]
    exact lt_of_lt_of_le hq' (min_le_left _ _)
  · intro i hi
    dsimp only
    have h1 := Finset.mem_filter.1 hi
    have hiv : i < v := Finset.mem_range.1 h1.1
    have hin : i < w.length := hiv.trans hvn
    have hiA : w.idxOf i < (w.take k).length := by
      rw [hlen]
      exact lt_min h1.2 (hw.idxOf_lt hin)
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inl ?_⟩
    rw [show (w.take k)[w.idxOf i]'hiA = i by rw [hAget _ hiA, hw.getD_idxOf hin],
      show (w.take k)[j]'hjA = v from hAget j hjA]
    exact hiv
  · rintro ⟨q, hq⟩ hmem
    have hqn : q < w.length := by
      rw [hlen] at hq
      omega
    refine Fin.ext ?_
    dsimp only
    rw [hAget q hq]
    exact hw.idxOf_getD hqn
  · intro i hi
    dsimp only
    have h1 := Finset.mem_filter.1 hi
    have hiv : i < v := Finset.mem_range.1 h1.1
    have hin : i < w.length := hiv.trans hvn
    have hiA : w.idxOf i < (w.take k).length := by
      rw [hlen]
      exact lt_min h1.2 (hw.idxOf_lt hin)
    rw [hAget _ hiA, hw.getD_idxOf hin]

/-- **Keeping the letters `< k` of the inverse of a standard word gives the inverse of the
standardisation of the prefix of length `k`.** -/
theorem ltFilter_invStd (hw : IsStd w) (k : ℕ) :
    ltFilter k (invStd w) = invStd (std (w.take k)) := by
  have hstd : IsStd (ltFilter k (invStd w)) := isStd_ltFilter_invStd hw
  have hlen : (ltFilter k (invStd w)).length = min k w.length := length_ltFilter_invStd hw
  have key : invStd (ltFilter k (invStd w)) = std (w.take k) := by
    refine List.ext_getElem (by simp [hlen]) fun j h1 h2 => ?_
    have hj : j < min k w.length := by
      rw [length_invStd, hlen] at h1
      exact h1
    rw [getElem_invStd, idxOf_ltFilter_invStd hw hj, ← getElem_std_take hw hj]
  calc ltFilter k (invStd w)
      = invStd (invStd (ltFilter k (invStd w))) := (invStd_invStd hstd).symm
    _ = invStd (std (w.take k)) := by rw [key]

end List
