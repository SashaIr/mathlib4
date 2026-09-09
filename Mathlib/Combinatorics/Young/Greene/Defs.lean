/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Order.Lattice.Nat

/-!
# Greene invariants: definitions

A Lean 4 port of the beginning of `theories/LRrule/Greene.v` from
[Coq-Combi](https://github.com/math-comp/Coq-Combi).

Greene's theorem computes, for a word `w` and an integer `k`, the maximal total size of a
union of `k` nondecreasing subsequences of `w`.  We encode such a union as a *colouring* of
the positions of `w`: a function `c : ℕ → Option ℕ` assigning to each position either no
colour or a colour `< k`, in such a way that the letters carrying a fixed colour are
nondecreasing.

## Main definitions

* `List.IsGreeneCol w k c` : `c` is a `k`-colouring of the positions of `w`.
* `List.greeneSize w c` : the number of coloured positions.
* `List.greeneRow w k` : the Greene invariant, the maximum of `greeneSize` over the
  `k`-colourings of `w`.
-/

@[expose] public section

namespace List

variable {T : Type*} [LinearOrder T]

/-- A `k`-colouring of the positions of `w`: each position receives a colour `< k` or no
colour at all, and the positions carrying a given colour carry nondecreasing letters, i.e.
they form a nondecreasing subsequence of `w`. -/
def IsGreeneCol (w : List T) (k : ℕ) (c : ℕ → Option ℕ) : Prop :=
  (∀ i x, c i = some x → x < k) ∧
    ∀ i j x (hij : i < j) (hj : j < w.length), c i = some x → c j = some x →
      w[i]'(hij.trans hj) ≤ w[j]

lemma IsGreeneCol.lt_of_colour {w : List T} {k : ℕ} {c : ℕ → Option ℕ} (h : IsGreeneCol w k c)
    {i x : ℕ} (hi : c i = some x) : x < k := h.1 i x hi

lemma IsGreeneCol.le_of_colour {w : List T} {k : ℕ} {c : ℕ → Option ℕ} (h : IsGreeneCol w k c)
    {i j x : ℕ} (hij : i < j) (hj : j < w.length) (hi : c i = some x) (hjc : c j = some x) :
    w[i]'(hij.trans hj) ≤ w[j] := h.2 i j x hij hj hi hjc

/-- The colouring with no coloured position at all. -/
lemma isGreeneCol_none (w : List T) (k : ℕ) : IsGreeneCol w k (fun _ => none) :=
  ⟨by simp, by simp⟩

/-- The number of coloured positions of `w`. -/
def greeneSize (w : List T) (c : ℕ → Option ℕ) : ℕ :=
  ((Finset.range w.length).filter fun i => (c i).isSome).card

omit [LinearOrder T] in
lemma greeneSize_le_length (w : List T) (c : ℕ → Option ℕ) : greeneSize w c ≤ w.length := by
  refine le_trans (Finset.card_filter_le _ _) ?_
  simp

/-- The set of sizes of the `k`-colourings of `w`. -/
def greeneSet (w : List T) (k : ℕ) : Set ℕ :=
  {m | ∃ c, IsGreeneCol w k c ∧ greeneSize w c = m}

lemma greeneSet_nonempty (w : List T) (k : ℕ) : (greeneSet w k).Nonempty :=
  ⟨_, ⟨_, isGreeneCol_none w k, rfl⟩⟩

lemma greeneSet_bddAbove (w : List T) (k : ℕ) : BddAbove (greeneSet w k) := by
  refine ⟨w.length, ?_⟩
  rintro m ⟨c, -, rfl⟩
  exact greeneSize_le_length w c

/-- The Greene invariant of a word: the maximal total number of positions covered by `k`
disjoint nondecreasing subsequences of `w` (Coq `Greene_row`). -/
noncomputable def greeneRow (w : List T) (k : ℕ) : ℕ := sSup (greeneSet w k)

lemma greeneRow_mem (w : List T) (k : ℕ) : greeneRow w k ∈ greeneSet w k :=
  Nat.sSup_mem (greeneSet_nonempty w k) (greeneSet_bddAbove w k)

/-- The Greene invariant is attained by some colouring. -/
lemma exists_greeneCol (w : List T) (k : ℕ) :
    ∃ c, IsGreeneCol w k c ∧ greeneSize w c = greeneRow w k := greeneRow_mem w k

lemma le_greeneRow {w : List T} {k : ℕ} {c : ℕ → Option ℕ} (h : IsGreeneCol w k c) :
    greeneSize w c ≤ greeneRow w k :=
  le_csSup (greeneSet_bddAbove w k) ⟨c, h, rfl⟩

lemma greeneRow_le {w : List T} {k N : ℕ}
    (h : ∀ c, IsGreeneCol w k c → greeneSize w c ≤ N) : greeneRow w k ≤ N := by
  obtain ⟨c, hc, hsize⟩ := exists_greeneCol w k
  exact hsize ▸ h c hc

lemma greeneRow_le_length (w : List T) (k : ℕ) : greeneRow w k ≤ w.length :=
  greeneRow_le fun c _ => greeneSize_le_length w c

@[simp] lemma greeneRow_nil (k : ℕ) : greeneRow ([] : List T) k = 0 := by
  simpa using greeneRow_le_length ([] : List T) k

@[simp] lemma greeneRow_zero (w : List T) : greeneRow w 0 = 0 := by
  refine Nat.le_zero.1 (greeneRow_le fun c hc => ?_)
  refine Nat.le_zero.2 (Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 ?_))
  intro i _
  cases hci : c i with
  | none => simp
  | some x => exact absurd (hc.lt_of_colour hci) (Nat.not_lt_zero x)

/-- The Greene invariant is nondecreasing in the number of colours. -/
lemma greeneRow_mono (w : List T) {k l : ℕ} (h : k ≤ l) : greeneRow w k ≤ greeneRow w l := by
  refine greeneRow_le fun c hc => le_greeneRow ⟨fun i x hx => (hc.lt_of_colour hx).trans_le h, hc.2⟩

end List
