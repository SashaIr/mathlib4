/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.Shape.Dominance
import Mathlib.Combinatorics.Young.Greene.Invariance
import Mathlib.Combinatorics.Young.Greene.Tableau

/-!
# Greene's theorem for rows

A Lean 4 port of the row case of `theories/LRrule/Greene_inv.v` from
[Coq-Combi](https://github.com/math-comp/Coq-Combi).

Greene's invariant `List.greeneRow w k` is the maximal number of letters of the word `w`
that can be covered by `k` nondecreasing subsequences.  Greene's theorem states that this
number equals the sum of the `k` first parts of the shape of the Robinson-Schensted
tableau `List.RS w`.

## Main results

* `List.greeneRow_eq_sum_take_shape` : **Greene's theorem** (Coq `Greene_row_RS`),
  `greeneRow w k = ((shape (RS w)).take k).sum`.
* `List.greeneRow_one` : the case `k = 1` recovers Schensted's theorem, the Greene
  invariant `greeneRow w 1` is the maximal length of a nondecreasing subsequence of `w`.
-/

namespace List

open List

variable {T : Type*} [LinearOrder T]

/-- The sum of the `k` first entries of a list of naturals, as a sum over a range. -/
lemma sum_take_eq_sum_range_getD (l : List ℕ) (k : ℕ) :
    (l.take k).sum = ∑ r ∈ Finset.range (min k l.length), l.getD r 0 := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih =>
    cases k with
    | zero => simp
    | succ m =>
      have hmin : min (m + 1) (a :: l).length = min m l.length + 1 := by
        simp only [List.length_cons]; omega
      rw [List.take_succ_cons, List.sum_cons, ih m, hmin, Finset.sum_range_succ']
      simp [Nat.add_comm]

omit [LinearOrder T] in
/-- The sum of the `k` first parts of the shape of a tableau. -/
lemma sum_take_shape (t : List (List T)) (k : ℕ) :
    ((shape t).take k).sum = ∑ r ∈ Finset.range (min k t.length), rowLen t r := by
  rw [sum_take_eq_sum_range_getD, length_shape]
  exact Finset.sum_congr rfl fun r _ => getD_shape t r

/-- **Greene's theorem** for rows: the maximal number of letters of `w` that can be covered
by `k` nondecreasing subsequences is the sum of the `k` first parts of the shape of the
Robinson-Schensted tableau of `w` (Coq `Greene_row_RS`). -/
theorem greeneRow_eq_sum_take_shape (w : List T) (k : ℕ) :
    greeneRow w k = ((shape (RS w)).take k).sum := by
  rw [← greeneRow_placticEquiv (plactic_toWord_RS w) k,
    greeneRow_toWord (isTableau_RS w) k, sum_take_shape]

/-- Greene's invariant for `k = 1` is the length of the first row of the Robinson-Schensted
tableau, that is, the length of the Schensted row of `w`. -/
theorem greeneRow_one_eq_length_schensted (w : List T) :
    greeneRow w 1 = (schensted w).length := by
  rw [greeneRow_eq_sum_take_shape, ← headD_RS]
  cases h : RS w with
  | nil => simp [shape]
  | cons r t => simp [shape]

/-- Greene's theorem for `k = 1` is Schensted's theorem: `greeneRow w 1` is the maximal
length of a nondecreasing subsequence of `w`. -/
theorem greeneRow_one (w : List T) :
    IsGreatest {n : ℕ | ∃ s : List T, s.Sublist w ∧ s.Pairwise (· ≤ ·) ∧ s.length = n}
      (greeneRow w 1) := by
  rw [greeneRow_one_eq_length_schensted]
  exact schensted_isGreatest w

/-- The shape of the Robinson-Schensted tableau is determined by the Greene row invariants:
its `k`-th part is the increment of `greeneRow w` at `k`. -/
theorem getD_shape_RS (w : List T) (k : ℕ) :
    (shape (RS w)).getD k 0 = greeneRow w (k + 1) - greeneRow w k := by
  rw [greeneRow_eq_sum_take_shape, greeneRow_eq_sum_take_shape, sum_take_succ_getD]
  omega

/-- Two words have Robinson-Schensted tableaux of the same shape exactly when they have the
same Greene row invariants. -/
theorem shape_RS_eq_iff_greeneRow_eq {u v : List T} :
    shape (RS u) = shape (RS v) ↔ ∀ k, greeneRow u k = greeneRow v k := by
  constructor
  · intro h k
    rw [greeneRow_eq_sum_take_shape, greeneRow_eq_sum_take_shape, h]
  · intro h
    refine IsPart.ext_getD (isPart_shape (isTableau_RS u)) (isPart_shape (isTableau_RS v))
      fun k => ?_
    rw [getD_shape_RS, getD_shape_RS, h, h]

end List
