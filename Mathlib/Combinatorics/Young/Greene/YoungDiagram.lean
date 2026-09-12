/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram
public import Mathlib.Combinatorics.Young.Greene.ColumnTheorem
public import Mathlib.Combinatorics.Young.Greene.Theorem

/-!
# Greene's theorem for Young diagrams

`Mathlib.Combinatorics.Young.Greene.Theorem` and
`Mathlib.Combinatorics.Young.Greene.ColumnTheorem` prove Greene's theorem with the shape of
the Robinson–Schensted tableau of a word given as a weakly decreasing list.  This file
restates both halves with the bundled types: the shape of `Young.RS w` is a `YoungDiagram`
(`Young.rsDiagram`), respectively a partition of the length of `w` (`Young.rsPartition`),
Greene's row invariant is the sum of its first row lengths, and Greene's column invariant is
the sum of its first column lengths — no conjugate partition appears, because conjugation is
transposition and the parts of the conjugate are the column lengths.

## Main definitions

* `Young.rsDiagram w` : the shape of the Robinson–Schensted tableau of `w`, as a Young
  diagram.
* `Young.rsPartition w` : the same shape, as a partition of `w.length`.

## Main results

* `Young.greeneRow_eq_sum_rowLen` : **Greene's theorem for rows**,
  `greeneRow w k = ∑ r < k, (rsDiagram w).rowLen r`.
* `Young.greeneCol_eq_sum_colLen` : **Greene's theorem for columns**,
  `greeneCol w k = ∑ c < k, (rsDiagram w).colLen c`.
* `Young.rsDiagram_eq_iff_greeneRow_eq` : two words have the same Robinson–Schensted shape
  exactly when they have the same Greene row invariants.

## References

* [C. Greene, *An extension of Schensted's theorem*][greene1974]
* [B. E. Sagan, *The symmetric group*][sagan2001]
* [F. Hivert et al., *Coq-Combi*][hivert-coqcombi]
-/

@[expose] public section

namespace Young

open List YoungDiagram

variable {T : Type*} [LinearOrder T]

/-- The sum of the first `k` entries of a list of naturals, as a sum over `Finset.range k`;
the entries beyond the end of the list are `0`, so no truncation of `k` is needed. -/
lemma sum_take_eq_sum_range_getD' (l : List ℕ) (k : ℕ) :
    (l.take k).sum = ∑ r ∈ Finset.range k, l.getD r 0 := by
  rw [sum_take_eq_sum_range_getD]
  have hsub : Finset.range (min k l.length) ⊆ Finset.range k := fun x hx =>
    Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hx) (min_le_left k l.length))
  refine Finset.sum_subset hsub fun r hr hr' => ?_
  simp only [Finset.mem_range, not_lt] at hr hr'
  exact List.getD_eq_default _ _ (by omega)

/-! ### The Robinson–Schensted shape as a Young diagram -/

/-- The shape of the Robinson–Schensted tableau of `w`, as a Young diagram. -/
def rsDiagram (w : List T) : YoungDiagram :=
  ofRowLens (shape (RS w)) (isPart_shape (isTableau_RS w)).sortedGE

@[simp] lemma rowLens_rsDiagram (w : List T) : (rsDiagram w).rowLens = shape (RS w) :=
  rowLens_ofRowLens_eq_self (isPart_shape (isTableau_RS w)).2

@[simp] lemma rowLen_rsDiagram (w : List T) (r : ℕ) :
    (rsDiagram w).rowLen r = (shape (RS w)).getD r 0 :=
  rowLen_ofRowLens_eq_getD (isPart_shape (isTableau_RS w)) r

@[simp] lemma colLen_rsDiagram (w : List T) (c : ℕ) :
    (rsDiagram w).colLen c = (conjPart (shape (RS w))).getD c 0 :=
  colLen_ofRowLens_eq_getD_conjPart (isPart_shape (isTableau_RS w)) c

/-- The Robinson–Schensted diagram of `w` has one box per letter of `w`. -/
@[simp] theorem card_rsDiagram (w : List T) : (rsDiagram w).card = w.length := by
  rw [rsDiagram, card_ofRowLens_eq_sum (isPart_shape (isTableau_RS w))]
  exact sizeTab_RS w

/-- The shape of the Robinson–Schensted tableau of `w`, as a partition of `w.length`. -/
def rsPartition (w : List T) : Nat.Partition w.length :=
  Nat.Partition.ofList (shape (RS w)) (isPart_shape (isTableau_RS w)) (sizeTab_RS w)

@[simp] lemma partsList_rsPartition (w : List T) :
    (rsPartition w).partsList = shape (RS w) :=
  Nat.Partition.partsList_ofList _ _

@[simp] lemma youngDiagram_rsPartition (w : List T) :
    (rsPartition w).youngDiagram = rsDiagram w := by
  rw [Nat.Partition.youngDiagram, rsDiagram]
  exact ofRowLens_congr (Nat.Partition.isPart_partsList _) (isPart_shape (isTableau_RS w))
    (partsList_rsPartition w)

/-! ### Greene's theorem -/

/-- **Greene's theorem** for rows: the maximal number of letters of `w` that can be covered
by `k` nondecreasing subsequences is the total length of the first `k` rows of the
Robinson–Schensted diagram of `w`. -/
theorem greeneRow_eq_sum_rowLen (w : List T) (k : ℕ) :
    greeneRow w k = ∑ r ∈ Finset.range k, (rsDiagram w).rowLen r := by
  simp only [rowLen_rsDiagram]
  rw [greeneRow_eq_sum_take_shape, sum_take_eq_sum_range_getD']

/-- **Greene's theorem** for columns: the maximal number of letters of `w` that can be
covered by `k` strictly decreasing subsequences is the total length of the first `k` columns
of the Robinson–Schensted diagram of `w`. -/
theorem greeneCol_eq_sum_colLen (w : List T) (k : ℕ) :
    greeneCol w k = ∑ c ∈ Finset.range k, (rsDiagram w).colLen c := by
  simp only [colLen_rsDiagram]
  rw [greeneCol_eq_sum_take_conjPart, sum_take_eq_sum_range_getD']

/-- The `k`-th row of the Robinson–Schensted diagram is the increment of Greene's row
invariant at `k`. -/
theorem rowLen_rsDiagram_eq_sub (w : List T) (k : ℕ) :
    (rsDiagram w).rowLen k = greeneRow w (k + 1) - greeneRow w k := by
  rw [rowLen_rsDiagram, getD_shape_RS]

/-- The `k`-th column of the Robinson–Schensted diagram is the increment of Greene's column
invariant at `k`. -/
theorem colLen_rsDiagram_eq_sub (w : List T) (k : ℕ) :
    (rsDiagram w).colLen k = greeneCol w (k + 1) - greeneCol w k := by
  rw [colLen_rsDiagram, getD_conjPart_shape_RS]

/-- Two words have Robinson–Schensted tableaux of the same shape exactly when they have the
same Greene row invariants. -/
theorem rsDiagram_eq_iff_greeneRow_eq {u v : List T} :
    rsDiagram u = rsDiagram v ↔ ∀ k, greeneRow u k = greeneRow v k := by
  rw [← shape_RS_eq_iff_greeneRow_eq]
  constructor
  · intro h
    exact eq_of_ofRowLens_eq (isPart_shape (isTableau_RS u)) (isPart_shape (isTableau_RS v)) h
  · intro h
    exact ofRowLens_congr (isPart_shape (isTableau_RS u)) (isPart_shape (isTableau_RS v)) h

end Young
