/-
Copyright (c) 2026 Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.Greene.Defs

/-!
# Greene column invariants: definitions

A Lean 4 port of the column case of `theories/LRrule/Greene.v` from
[Coq-Combi](https://github.com/math-comp/Coq-Combi).

The column analogue of the Greene invariants replaces nondecreasing subsequences by
*strictly decreasing* ones: `List.greeneCol w k` is the maximal total number of letters of
`w` that can be covered by `k` strictly decreasing subsequences.  As in the row case a
union of `k` such subsequences is encoded by a colouring of the positions of `w` by `k`
colours.

## Main definitions

* `List.IsGreeneDecCol w k c` : `c` is a `k`-colouring of the positions of `w` whose
  colour classes are strictly decreasing.
* `List.greeneCol w k` : the Greene column invariant.
-/

namespace List

variable {T : Type*} [LinearOrder T]

/-- A `k`-colouring of the positions of `w` whose colour classes are strictly decreasing:
each position receives a colour `< k` or no colour at all, and if two positions `i < j`
carry the same colour then `w[j] < w[i]`. -/
def IsGreeneDecCol (w : List T) (k : ℕ) (c : ℕ → Option ℕ) : Prop :=
  (∀ i x, c i = some x → x < k) ∧
    ∀ i j x (hij : i < j) (hj : j < w.length), c i = some x → c j = some x →
      w[j] < w[i]'(hij.trans hj)

lemma IsGreeneDecCol.lt_of_colour {w : List T} {k : ℕ} {c : ℕ → Option ℕ}
    (h : IsGreeneDecCol w k c) {i x : ℕ} (hi : c i = some x) : x < k := h.1 i x hi

lemma IsGreeneDecCol.gt_of_colour {w : List T} {k : ℕ} {c : ℕ → Option ℕ}
    (h : IsGreeneDecCol w k c) {i j x : ℕ} (hij : i < j) (hj : j < w.length)
    (hi : c i = some x) (hjc : c j = some x) : w[j] < w[i]'(hij.trans hj) :=
  h.2 i j x hij hj hi hjc

/-- The colouring with no coloured position at all. -/
lemma isGreeneDecCol_none (w : List T) (k : ℕ) : IsGreeneDecCol w k (fun _ => none) :=
  ⟨by simp, by simp⟩

/-- The set of sizes of the strictly decreasing `k`-colourings of `w`. -/
def greeneColSet (w : List T) (k : ℕ) : Set ℕ :=
  {m | ∃ c, IsGreeneDecCol w k c ∧ greeneSize w c = m}

lemma greeneColSet_nonempty (w : List T) (k : ℕ) : (greeneColSet w k).Nonempty :=
  ⟨_, ⟨_, isGreeneDecCol_none w k, rfl⟩⟩

lemma greeneColSet_bddAbove (w : List T) (k : ℕ) : BddAbove (greeneColSet w k) := by
  refine ⟨w.length, ?_⟩
  rintro m ⟨c, -, rfl⟩
  exact greeneSize_le_length w c

/-- The Greene column invariant of a word: the maximal total number of positions covered by
`k` strictly decreasing subsequences of `w` (Coq `Greene_col`). -/
noncomputable def greeneCol (w : List T) (k : ℕ) : ℕ := sSup (greeneColSet w k)

lemma greeneCol_mem (w : List T) (k : ℕ) : greeneCol w k ∈ greeneColSet w k :=
  Nat.sSup_mem (greeneColSet_nonempty w k) (greeneColSet_bddAbove w k)

/-- The Greene column invariant is attained by some colouring. -/
lemma exists_greeneDecCol (w : List T) (k : ℕ) :
    ∃ c, IsGreeneDecCol w k c ∧ greeneSize w c = greeneCol w k := greeneCol_mem w k

lemma le_greeneCol {w : List T} {k : ℕ} {c : ℕ → Option ℕ} (h : IsGreeneDecCol w k c) :
    greeneSize w c ≤ greeneCol w k :=
  le_csSup (greeneColSet_bddAbove w k) ⟨c, h, rfl⟩

lemma greeneCol_le {w : List T} {k N : ℕ}
    (h : ∀ c, IsGreeneDecCol w k c → greeneSize w c ≤ N) : greeneCol w k ≤ N := by
  obtain ⟨c, hc, hsize⟩ := exists_greeneDecCol w k
  exact hsize ▸ h c hc

lemma greeneCol_le_length (w : List T) (k : ℕ) : greeneCol w k ≤ w.length :=
  greeneCol_le fun c _ => greeneSize_le_length w c

@[simp] lemma greeneCol_nil (k : ℕ) : greeneCol ([] : List T) k = 0 := by
  simpa using greeneCol_le_length ([] : List T) k

@[simp] lemma greeneCol_zero (w : List T) : greeneCol w 0 = 0 := by
  refine Nat.le_zero.1 (greeneCol_le fun c hc => ?_)
  refine Nat.le_zero.2 (Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 ?_))
  intro i _
  cases hci : c i with
  | none => simp
  | some x => exact absurd (hc.lt_of_colour hci) (Nat.not_lt_zero x)

/-- The Greene column invariant is nondecreasing in the number of colours. -/
lemma greeneCol_mono (w : List T) {k l : ℕ} (h : k ≤ l) : greeneCol w k ≤ greeneCol w l :=
  greeneCol_le fun _ hc => le_greeneCol ⟨fun _ _ hx => (hc.lt_of_colour hx).trans_le h, hc.2⟩

end List
