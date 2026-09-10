/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.Shape.Conjugate
public import Mathlib.Logic.Equiv.Defs

/-!
# Conjugation as a bijection of partitions

A complement to `Mathlib.Combinatorics.Young.Shape.Conjugate`, in the spirit of
[Coq-Combi](https://github.com/math-comp/Coq-Combi) (`theories/Combi/partition.v`),
where conjugation is packaged as an involution of the finite type of partitions
of an integer.

Here we package conjugation of partitions as an explicit `Equiv`.

## Main results

* `Young.conjPartEquiv` : conjugation is an involutive bijection of the partitions of `n`.
* `Young.conjPartEquivLengthLe` : conjugation is a bijection between the partitions of `n`
  with at most `k` parts and the partitions of `n` all of whose parts are at most `k`.
-/

@[expose] public section

namespace Young

open List

/-- The parts of a partition are bounded by its first part. -/
lemma IsPart.forall_mem_le_iff {sh : List ℕ} (h : IsPart sh) (k : ℕ) :
    (∀ i ∈ sh, i ≤ k) ↔ sh.headD 0 ≤ k := by
  constructor
  · intro hall
    cases sh with
    | nil => simp
    | cons a s => exact hall a (by simp)
  · intro hhead i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hi
    have hmono := h.getD_antitone (i := 0) (j := j) (Nat.zero_le _)
    rw [List.getD_eq_getElem _ _ hj] at hmono
    have h0 : sh.getD 0 0 = sh.headD 0 := by cases sh <;> simp
    rw [h0] at hmono
    exact le_trans hmono hhead

/-- The first part of the conjugate of a partition is its number of parts. -/
lemma headD_conjPart {sh : List ℕ} (h : IsPart sh) : (conjPart sh).headD 0 = sh.length := by
  have := length_conjPart (isPart_conjPart h)
  rw [conjPart_conjPart h] at this
  exact this.symm

/-- Conjugation is an involutive bijection of the set of partitions of `n`. -/
def conjPartEquiv (n : ℕ) :
    {p : List ℕ // IsPart p ∧ p.sum = n} ≃ {p : List ℕ // IsPart p ∧ p.sum = n} where
  toFun p := ⟨conjPart p.1, isPart_conjPart p.2.1, by rw [sum_conjPart]; exact p.2.2⟩
  invFun p := ⟨conjPart p.1, isPart_conjPart p.2.1, by rw [sum_conjPart]; exact p.2.2⟩
  left_inv p := Subtype.ext (conjPart_conjPart p.2.1)
  right_inv p := Subtype.ext (conjPart_conjPart p.2.1)

@[simp] lemma conjPartEquiv_apply {n : ℕ} (p : {p : List ℕ // IsPart p ∧ p.sum = n}) :
    ((conjPartEquiv n) p).1 = conjPart p.1 := rfl

/-- Conjugation is a bijection between the partitions of `n` with at most `k` parts and the
partitions of `n` all of whose parts are at most `k`.  In particular these two sets of
partitions are equinumerous. -/
def conjPartEquivLengthLe (n k : ℕ) :
    {p : List ℕ // IsPart p ∧ p.sum = n ∧ p.length ≤ k} ≃
      {p : List ℕ // IsPart p ∧ p.sum = n ∧ ∀ i ∈ p, i ≤ k} where
  toFun p :=
    ⟨conjPart p.1, isPart_conjPart p.2.1, by rw [sum_conjPart]; exact p.2.2.1, by
      rw [(isPart_conjPart p.2.1).forall_mem_le_iff, headD_conjPart p.2.1]
      exact p.2.2.2⟩
  invFun p :=
    ⟨conjPart p.1, isPart_conjPart p.2.1, by rw [sum_conjPart]; exact p.2.2.1, by
      rw [length_conjPart p.2.1]
      exact (p.2.1.forall_mem_le_iff k).1 p.2.2.2⟩
  left_inv p := Subtype.ext (conjPart_conjPart p.2.1)
  right_inv p := Subtype.ext (conjPart_conjPart p.2.1)

@[simp] lemma conjPartEquivLengthLe_apply {n k : ℕ}
    (p : {p : List ℕ // IsPart p ∧ p.sum = n ∧ p.length ≤ k}) :
    ((conjPartEquivLengthLe n k) p).1 = conjPart p.1 := rfl

end Young
