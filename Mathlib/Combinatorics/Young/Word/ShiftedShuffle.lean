/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.Word.Standardization
public import Mathlib.Data.List.Shuffle

/-!
# The shifted shuffle of two words

A Lean 4 port of the shifted shuffle `shsh` of `theories/LRrule/shuffle.v` from
[Coq-Combi](https://github.com/math-comp/Coq-Combi).

The *shifted shuffle* of two words `u` and `v` over the natural numbers is the set of the
shuffles of `u` with the word obtained from `v` by adding `|u|` to each of its letters.  It
is the operation underlying the Littlewood–Richardson rule for the free Schur functions:
when `u` is a standard word of length `n`, its letters are exactly `0, …, n-1`, so a word
belongs to the shifted shuffle of `u` and `v` exactly when its letters `< n` spell `u` and
its letters `≥ n`, shifted down by `n`, spell `v`.

## Main definitions

* `Young.shiftn n s` : shift all the letters of `s` up by `n` (Coq `shiftn`).
* `Young.sfilterleq n s` : keep the letters of `s` that are at least `n` and shift them down
  by `n` (Coq `sfilterleq`).
* `Young.shsh u v` : the shifted shuffle of `u` and `v` (Coq `shsh`).

## Main results

* `Young.mem_shsh` : the characterisation of the words in a shifted shuffle
  (Coq `mem_shsh`).
* `Young.IsStd.mem_shsh` : the same, for `u` a standard word.
* `Young.reverse_mem_shsh` : reversing a word of a shifted shuffle gives a word of the
  shifted shuffle of the reversed words.
* `Young.IsStd.of_mem_shsh` : a shifted shuffle of two standard words is standard
  (Coq `std_shsh`).
-/

@[expose] public section

namespace Young

open List

variable {u v w : List ℕ} {n : ℕ}

/-! ### Shifting the letters of a word -/

/-- Shift all the letters of the word `s` up by `n` (Coq `shiftn`). -/
def shiftn (n : ℕ) (s : List ℕ) : List ℕ := s.map (n + ·)

@[simp] lemma length_shiftn (n : ℕ) (s : List ℕ) : (shiftn n s).length = s.length := by
  simp [shiftn]

@[simp] lemma shiftn_nil (n : ℕ) : shiftn n [] = [] := rfl

lemma mem_shiftn {x : ℕ} : x ∈ shiftn n v ↔ ∃ y ∈ v, x = n + y := by
  simp only [shiftn, List.mem_map, eq_comm]

lemma le_of_mem_shiftn {x : ℕ} (hx : x ∈ shiftn n v) : n ≤ x := by
  obtain ⟨y, -, rfl⟩ := mem_shiftn.1 hx
  omega

/-- Keep the letters of `s` that are at least `n`, and shift them down by `n`
(Coq `sfilterleq`). -/
def sfilterleq (n : ℕ) (s : List ℕ) : List ℕ :=
  (s.filter fun x => decide (n ≤ x)).map (· - n)

@[simp] lemma sfilterleq_shiftn (n : ℕ) (v : List ℕ) : sfilterleq n (shiftn n v) = v := by
  rw [sfilterleq, List.filter_eq_self.2 fun x hx => by simpa using le_of_mem_shiftn hx]
  simp [shiftn, Function.comp_def]

/-- Shifting back the letters that are at least `n` recovers them. -/
lemma shiftn_map_sub (hl : ∀ x ∈ w, n ≤ x) : shiftn n (w.map (· - n)) = w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have ha : n ≤ a := hl a (by simp)
    rw [List.map_cons, shiftn, List.map_cons, ← shiftn, ih fun x hx => hl x (by simp [hx])]
    congr 1
    omega

/-! ### The shifted shuffle -/

/-- The shifted shuffle of `u` and `v`: the shuffles of `u` with the word `v` shifted up by
the length of `u` (Coq `shsh`). -/
def shsh (u v : List ℕ) : List (List ℕ) := shuffle u (shiftn u.length v)

lemma perm_of_mem_shsh (h : w ∈ shsh u v) : w.Perm (u ++ shiftn u.length v) :=
  perm_append_of_mem_shuffle h

lemma length_of_mem_shsh (h : w ∈ shsh u v) : w.length = u.length + v.length := by
  simpa using (perm_of_mem_shsh h).length_eq

/-- The two halves of a word of the shifted shuffle, as filters. -/
private lemma not_lt_pred (n : ℕ) : (fun x : ℕ => !decide (x < n)) = fun x => decide (n ≤ x) := by
  funext x
  rcases Nat.lt_or_ge x n with h | h
  · simp [h, Nat.not_le.2 h]
  · simp [Nat.not_lt.2 h, h]

/-- **The characterisation of the words of a shifted shuffle** (Coq `mem_shsh`): if all the
letters of `u` are smaller than its length, a word `w` is a shifted shuffle of `u` and `v`
exactly when its letters `< |u|` spell `u` and its letters `≥ |u|`, shifted down, spell
`v`. -/
theorem mem_shsh (hu : ∀ x ∈ u, x < u.length) :
    w ∈ shsh u v ↔
      w.filter (fun x => decide (x < u.length)) = u ∧ sfilterleq u.length w = v := by
  rw [shsh, mem_shuffle_iff]
  constructor
  · intro h
    have hu' : ∀ x ∈ u, decide (x < u.length) = true := fun x hx => by simpa using hu x hx
    have hv' : ∀ x ∈ shiftn u.length v, decide (x < u.length) = false := fun x hx => by
      have := le_of_mem_shiftn hx
      simpa using this
    refine ⟨h.filter_eq_left hu' hv', ?_⟩
    have hright := h.filter_eq_right hu' hv'
    rw [not_lt_pred] at hright
    rw [sfilterleq, hright, shiftn, List.map_map]
    simp [Function.comp_def]
  · rintro ⟨hf, hs⟩
    have hgen := isShuffle_filter (fun x : ℕ => decide (x < u.length)) w
    rw [not_lt_pred, hf] at hgen
    have hle : ∀ x ∈ w.filter fun x => decide (u.length ≤ x), u.length ≤ x := by
      intro x hx
      simpa using (List.mem_filter.1 hx).2
    have : shiftn u.length v = w.filter fun x => decide (u.length ≤ x) := by
      rw [← hs, sfilterleq, shiftn_map_sub hle]
    rwa [this]

/-- The characterisation of the words of a shifted shuffle, for `u` a standard word. -/
theorem IsStd.mem_shsh (hu : IsStd u) :
    w ∈ shsh u v ↔
      w.filter (fun x => decide (x < u.length)) = u ∧ sfilterleq u.length w = v :=
  Young.mem_shsh fun _ hx => mem_range.1 (hu.mem_iff.1 hx)

/-- **Reversing a word of a shifted shuffle** gives a word of the shifted shuffle of the
reversed words. -/
theorem reverse_mem_shsh (hu : ∀ x ∈ u, x < u.length) (h : w ∈ shsh u v) :
    w.reverse ∈ shsh u.reverse v.reverse := by
  rw [mem_shsh hu] at h
  rw [mem_shsh (by simpa using hu)]
  refine ⟨by rw [List.length_reverse, List.filter_reverse, h.1], ?_⟩
  rw [List.length_reverse, sfilterleq, List.filter_reverse, List.map_reverse, ← sfilterleq, h.2]

/-- **A shifted shuffle of two standard words is standard** (Coq `std_shsh`). -/
theorem IsStd.of_mem_shsh (hu : IsStd u) (hv : IsStd v) (h : w ∈ shsh u v) : IsStd w := by
  have hperm : w.Perm (u ++ shiftn u.length v) := perm_of_mem_shsh h
  have hrange : (u ++ shiftn u.length v).Perm (range (u.length + v.length)) := by
    rw [List.range_add]
    exact hu.append (hv.map _)
  have : w.Perm (range (u.length + v.length)) := hperm.trans hrange
  rw [IsStd, length_of_mem_shsh h]
  exact this

end Young
