/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.Greene.ColumnInvariance
public import Mathlib.Combinatorics.Young.Greene.ColumnTableau
public import Mathlib.Combinatorics.Young.Greene.Theorem
public import Mathlib.Combinatorics.Young.RobinsonSchensted.ColumnInsertion

/-!
# Greene's theorem for columns

A Lean 4 port of the column case of `theories/LRrule/Greene_inv.v` from
[Coq-Combi](https://github.com/math-comp/Coq-Combi).

The Greene column invariant `Young.greeneCol w k` is the maximal number of letters of the
word `w` that can be covered by `k` strictly decreasing subsequences.  Greene's theorem for
columns states that this number is the sum of the `k` first parts of the *conjugate* of the
shape of the Robinson-Schensted tableau `Young.RS w`.

## Main results

* `Young.greeneCol_eq_sum_take_conjPart` : **Greene's theorem for columns** (Coq
  `Greene_col_RS`), `greeneCol w k = ((conjPart (shape (RS w))).take k).sum`.
* `Young.greeneCol_one` : the case `k = 1` recovers the dual of Schensted's theorem, the
  invariant `greeneCol w 1` is the maximal length of a strictly decreasing subsequence.
-/

@[expose] public section

namespace Young

open List

variable {T : Type*} [LinearOrder T]

/-! ### A counting identity for the conjugate partition -/

/-- The value of the conjugate partition in the column `c` is the number of rows longer
than `c`. -/
lemma getD_conjPart_eq_card {sh : List ℕ} (h : IsPart sh) (c : ℕ) :
    (conjPart sh).getD c 0 = ((Finset.range sh.length).filter fun r => c < sh.getD r 0).card := by
  have hiff : ∀ r, c < sh.getD r 0 ↔ r < (conjPart sh).getD c 0 := by
    intro r
    have := getD_le_conjPart_iff h r c
    omega
  have hle : (conjPart sh).getD c 0 ≤ sh.length := by
    by_contra hcon
    have : sh.length < (conjPart sh).getD c 0 := by omega
    have hpos := (hiff sh.length).2 this
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (le_refl _)] at hpos
    simp at hpos
  have hfilter : ((Finset.range sh.length).filter fun r => c < sh.getD r 0)
      = Finset.range ((conjPart sh).getD c 0) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, hiff r]
    exact ⟨fun hr => hr.2, fun hr => ⟨lt_of_lt_of_le hr hle, hr⟩⟩
  rw [hfilter, Finset.card_range]

/-- The sum of the `k` first parts of the conjugate of a partition counts the boxes lying
in the `k` first columns. -/
lemma sum_range_getD_conjPart {sh : List ℕ} (h : IsPart sh) (k : ℕ) :
    ∑ c ∈ Finset.range k, (conjPart sh).getD c 0
      = ∑ r ∈ Finset.range sh.length, min (sh.getD r 0) k := by
  simp only [getD_conjPart_eq_card h, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Finset.card_filter, ← Finset.card_range (min (sh.getD r 0) k)]
  congr 1
  ext c
  simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
  tauto

/-- The sum of the `k` first parts of the conjugate shape of a tableau. -/
lemma sum_take_conjPart_shape {t : List (List T)} (ht : IsTableau t) (k : ℕ) :
    ((conjPart (shape t)).take k).sum = ∑ r ∈ Finset.range t.length, min (rowLen t r) k := by
  have hpart := isPart_shape ht
  have hsum : ((conjPart (shape t)).take k).sum
      = ∑ c ∈ Finset.range k, (conjPart (shape t)).getD c 0 := by
    rw [sum_take_eq_sum_range_getD]
    refine Finset.sum_subset ?_ ?_
    · intro c hc
      simp only [Finset.mem_range, lt_min_iff] at hc ⊢
      exact hc.1
    · intro c hc hcn
      simp only [Finset.mem_range, lt_min_iff, not_and, not_lt] at hc hcn
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (hcn hc)]
      rfl
  rw [hsum, sum_range_getD_conjPart hpart k, length_shape]
  exact Finset.sum_congr rfl fun r _ => by rw [getD_shape]; rfl

/-- **Greene's theorem** for columns: the maximal number of letters of `w` that can be
covered by `k` strictly decreasing subsequences is the sum of the `k` first parts of the
conjugate of the shape of the Robinson-Schensted tableau of `w` (Coq `Greene_col_RS`). -/
theorem greeneCol_eq_sum_take_conjPart (w : List T) (k : ℕ) :
    greeneCol w k = ((conjPart (shape (RS w))).take k).sum := by
  rw [← greeneCol_placticEquiv (plactic_toWord_RS w) k, greeneCol_toWord (isTableau_RS w) k]
  exact (sum_take_conjPart_shape (isTableau_RS w) k).symm

/-- Greene's column invariant for `k = 1` is the number of rows of the Robinson-Schensted
tableau. -/
theorem greeneCol_one_eq_length_RS (w : List T) : greeneCol w 1 = (RS w).length := by
  rw [greeneCol_eq_sum_take_conjPart, sum_take_conjPart_shape (isTableau_RS w)]
  have hpart := isPart_shape (isTableau_RS w)
  have hone : ∀ r ∈ Finset.range (RS w).length, min (rowLen (RS w) r) 1 = 1 := by
    intro r hr
    simp only [Finset.mem_range] at hr
    have heq : (shape (RS w)).getD r 0 = rowLen (RS w) r := getD_shape _ _
    have hpos : 0 < rowLen (RS w) r := by
      rw [← heq]
      exact hpart.getD_pos (by rwa [length_shape])
    omega
  rw [Finset.sum_congr rfl hone, Finset.sum_const, smul_eq_mul, Finset.card_range, mul_one]

/-- Greene's theorem for columns in the case `k = 1` is the dual of Schensted's theorem:
`greeneCol w 1` is the maximal length of a strictly decreasing subsequence of `w`. -/
theorem greeneCol_one (w : List T) : IsGreatest (decLengths w) (greeneCol w 1) := by
  rw [greeneCol_one_eq_length_RS]
  exact isGreatest_decLengths_RS w

/-- The conjugate shape of the Robinson-Schensted tableau is determined by the Greene
column invariants: its `k`-th part is the increment of `greeneCol w` at `k`. -/
theorem getD_conjPart_shape_RS (w : List T) (k : ℕ) :
    (conjPart (shape (RS w))).getD k 0 = greeneCol w (k + 1) - greeneCol w k := by
  rw [greeneCol_eq_sum_take_conjPart, greeneCol_eq_sum_take_conjPart, sum_take_succ_getD]
  omega

end Young
