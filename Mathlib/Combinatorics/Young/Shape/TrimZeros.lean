/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Combinatorics.Young.Shape.Basic
public import Mathlib.Data.List.DropRight

/-!
# Normalising a list of natural numbers by removing its trailing zeroes

Shapes of Young diagrams are represented by lists of natural numbers without trailing
zeroes (`List.IsPart`).  When a shape is produced pointwise (for instance as the list of
values of a function on an initial segment of `ℕ`), trailing zeroes have to be removed.
This file provides `List.trimZeros` and `List.shapeOfFn` for that purpose.

## Main definitions

* `List.trimZeros l` : the list `l` with its trailing zeroes removed.
* `List.shapeOfFn k f` : the shape whose `i`-th part is `f i` for `i < k`.

## Main results

* `List.getD_trimZeros`, `List.sum_trimZeros` : trimming changes neither the parts nor
  the sum.
* `List.getD_shapeOfFn`, `List.sum_shapeOfFn`, `List.isPart_shapeOfFn`.
-/

@[expose] public section

namespace List

open List

/-- Remove the trailing zeroes of a list of natural numbers. -/
def trimZeros (l : List ℕ) : List ℕ := l.rdropWhile (fun x => x == 0)

lemma trimZeros_prefix (l : List ℕ) : trimZeros l <+: l := List.rdropWhile_prefix _ l

lemma trimZeros_append (l : List ℕ) :
    trimZeros l ++ l.rtakeWhile (fun x => x == 0) = l :=
  List.rdropWhile_append_rtakeWhile

lemma mem_rtakeWhile_zero {l : List ℕ} {x : ℕ} (hx : x ∈ l.rtakeWhile (fun y => y == 0)) :
    x = 0 := by
  simpa using List.mem_rtakeWhile_imp hx

lemma length_trimZeros_le (l : List ℕ) : (trimZeros l).length ≤ l.length :=
  (trimZeros_prefix l).length_le

@[simp] lemma sum_trimZeros (l : List ℕ) : (trimZeros l).sum = l.sum := by
  conv_rhs => rw [← trimZeros_append l]
  rw [List.sum_append, List.sum_eq_zero (fun x hx => mem_rtakeWhile_zero hx), Nat.add_zero]

lemma getD_trimZeros (l : List ℕ) (i : ℕ) : (trimZeros l).getD i 0 = l.getD i 0 := by
  set t := trimZeros l with ht
  set s := l.rtakeWhile (fun y => y == 0) with hs
  have hl : t ++ s = l := trimZeros_append l
  have hzero : ∀ j, s.getD j 0 = 0 := by
    intro j
    by_cases hj : j < s.length
    · rw [List.getD_eq_getElem _ _ hj]
      exact mem_rtakeWhile_zero (List.getElem_mem hj)
    · exact List.getD_eq_default _ _ (not_lt.1 hj)
  rw [← hl]
  by_cases hi : i < t.length
  · exact (List.getD_append t s 0 i hi).symm
  · rw [List.getD_append_right t s 0 i (not_lt.1 hi), hzero,
      List.getD_eq_default _ _ (not_lt.1 hi)]

lemma getLastD_trimZeros_ne_zero (l : List ℕ) : (trimZeros l).getLastD 1 ≠ 0 := by
  cases h : trimZeros l with
  | nil => simp
  | cons a t =>
    have hne : trimZeros l ≠ [] := by rw [h]; simp
    have := List.rdropWhile_last_not (fun x => x == 0) l hne
    simp only [beq_iff_eq] at this
    have hlast : (a :: t).getLast (by simp) = (trimZeros l).getLast hne := by
      congr 1; simp [h]
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast (by simp), hlast]
    exact this

/-- The shape whose `i`-th part is `f i`, for `i < k` (trailing zeroes removed). -/
def shapeOfFn (k : ℕ) (f : ℕ → ℕ) : List ℕ := trimZeros (List.ofFn fun i : Fin k => f i)

lemma getD_shapeOfFn (k : ℕ) (f : ℕ → ℕ) (i : ℕ) :
    (shapeOfFn k f).getD i 0 = if i < k then f i else 0 := by
  rw [shapeOfFn, getD_trimZeros]
  by_cases hi : i < k
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), ite_eq_left hi]
    simp
  · rw [List.getD_eq_default _ _ (by simpa using not_lt.1 hi), ite_eq_right hi]

lemma length_shapeOfFn_le (k : ℕ) (f : ℕ → ℕ) : (shapeOfFn k f).length ≤ k := by
  rw [shapeOfFn]
  simpa using length_trimZeros_le (List.ofFn fun i : Fin k => f i)

@[simp] lemma sum_shapeOfFn (k : ℕ) (f : ℕ → ℕ) :
    (shapeOfFn k f).sum = ∑ i ∈ Finset.range k, f i := by
  rw [shapeOfFn, sum_trimZeros, List.sum_ofFn]
  exact (Finset.sum_range fun i => f i).symm

/-- If `f` is weakly decreasing then `shapeOfFn k f` is a partition. -/
lemma isPart_shapeOfFn {k : ℕ} {f : ℕ → ℕ} (hf : ∀ i, f (i + 1) ≤ f i) :
    IsPart (shapeOfFn k f) := by
  refine isPart_of_getD (getLastD_trimZeros_ne_zero _) fun i => ?_
  simp only [getD_shapeOfFn]
  split_ifs with h1 h2 h2
  · exact hf i
  · omega
  · exact Nat.zero_le _
  · exact le_rfl

/-- A partition is the shape of its own sequence of parts. -/
lemma shapeOfFn_getD {sh : List ℕ} (hsh : IsPart sh) {k : ℕ} (hk : sh.length ≤ k) :
    shapeOfFn k (fun i => sh.getD i 0) = sh := by
  refine ext_getD_of_getLastD_ne_zero (getLastD_trimZeros_ne_zero _) hsh.getLastD_ne_zero
    fun i => ?_
  rw [getD_shapeOfFn]
  split_ifs with h
  · rfl
  · exact (List.getD_eq_default _ _ (by omega)).symm

/-- The sum of a list of natural numbers as a sum of its parts. -/
lemma sum_eq_sum_range_getD_length (l : List ℕ) :
    l.sum = ∑ i ∈ Finset.range l.length, l.getD i 0 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']
    simp [Nat.add_comm]

lemma sum_eq_sum_range_getD (l : List ℕ) {k : ℕ} (hk : l.length ≤ k) :
    l.sum = ∑ i ∈ Finset.range k, l.getD i 0 := by
  rw [sum_eq_sum_range_getD_length l]
  refine Finset.sum_subset
    (fun x hx => Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hx) hk))
    fun i _ hi => ?_
  exact List.getD_eq_default _ _ (by simpa using hi)

end List
