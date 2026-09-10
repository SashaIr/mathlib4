/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.Shape.Basic

/-!
# The conjugate of a partition

A Lean 4 port of the conjugation part of `theories/Combi/partition.v` from
[Coq-Combi](https://github.com/math-comp/Coq-Combi).

## Main definitions

* `Young.incrFirstN μ n` : add one box to each of the first `n` rows of `μ`
  (Coq `incr_first_n`).
* `Young.conjPart μ` : the conjugate partition (Coq `conj_part`).

## Main results

* `Young.isPart_conjPart` : the conjugate of a partition is a partition.
* `Young.sum_conjPart` : conjugation preserves the size.
* `Young.length_conjPart` : the conjugate has `μ 0` parts.
* `Young.inShape_conjPart` : `(r, c)` is a box of `μ` iff `(c, r)` is a box of `conjPart μ`.
* `Young.conjPart_conjPart` : conjugation is an involution on partitions.
-/

@[expose] public section

namespace Young

open List

/-! ### Adding a box to each of the first `n` rows -/

/-- `incrFirstN μ n` adds one to each of the first `n` parts of `μ`, padding
with parts equal to `1` if `μ` has fewer than `n` parts. -/
def incrFirstN : List ℕ → ℕ → List ℕ
  | [], n => List.replicate n 1
  | s0 :: s, 0 => s0 :: s
  | s0 :: s, n + 1 => (s0 + 1) :: incrFirstN s n

@[simp] lemma incrFirstN_nil (n : ℕ) : incrFirstN [] n = List.replicate n 1 := rfl

@[simp] lemma incrFirstN_zero (μ : List ℕ) : incrFirstN μ 0 = μ := by
  cases μ <;> rfl

@[simp] lemma incrFirstN_cons_succ (s0 : ℕ) (s : List ℕ) (n : ℕ) :
    incrFirstN (s0 :: s) (n + 1) = (s0 + 1) :: incrFirstN s n := rfl

/-- Coq `nth_incr_first_n`. -/
lemma getD_incrFirstN (μ : List ℕ) (n i : ℕ) :
    (incrFirstN μ n).getD i 0 = if i < n then μ.getD i 0 + 1 else μ.getD i 0 := by
  induction μ generalizing n i with
  | nil =>
    simp only [incrFirstN_nil, List.getD_nil]
    rcases Nat.lt_or_ge i n with h | h
    · rw [ite_eq_left h, List.getD_eq_getElem _ _ (by simpa using h)]
      simp
    · rw [ite_eq_right (by omega), List.getD_eq_default _ _ (by simpa using h)]
  | cons a s ih =>
    cases n with
    | zero => simp
    | succ m =>
      cases i with
      | zero => simp
      | succ j => simpa using ih m j

/-- Coq `size_incr_first_n` (in a slightly more general form). -/
@[simp] lemma length_incrFirstN (μ : List ℕ) (n : ℕ) :
    (incrFirstN μ n).length = max μ.length n := by
  induction μ generalizing n with
  | nil => simp
  | cons a s ih =>
    cases n with
    | zero => simp
    | succ m => simp [ih m, Nat.succ_max_succ]

/-- Coq `sumn_incr_first_n`. -/
@[simp] lemma sum_incrFirstN (μ : List ℕ) (n : ℕ) : (incrFirstN μ n).sum = μ.sum + n := by
  induction μ generalizing n with
  | nil => simp
  | cons a s ih =>
    cases n with
    | zero => simp
    | succ m => simp only [incrFirstN_cons_succ, List.sum_cons, ih m]; omega

/-- Coq `is_part_nseq1`. -/
lemma isPart_replicate_one (n : ℕ) : IsPart (List.replicate n 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    refine ⟨?_, ih⟩
    cases m with
    | zero => simp
    | succ k => simp [List.replicate_succ]

/-- Coq `is_part_incr_first_n`. -/
lemma IsPart.incrFirstN {μ : List ℕ} (h : IsPart μ) (n : ℕ) : IsPart (incrFirstN μ n) := by
  rw [isPart_iff_getD_pos]
  refine ⟨fun i ↦ ?_, fun i hi ↦ ?_⟩
  · rw [getD_incrFirstN, getD_incrFirstN]
    have hmono := h.getD_succ_le i
    split_ifs with h1 h2 h2 <;> omega
  · rw [length_incrFirstN] at hi
    rw [getD_incrFirstN]
    split_ifs with h1
    · omega
    · exact h.getD_pos (by omega)

/-! ### The conjugate partition -/

/-- The conjugate of a partition: the transpose of its Young diagram
(Coq `conj_part`). -/
def conjPart : List ℕ → List ℕ
  | [] => []
  | s0 :: s => incrFirstN (conjPart s) s0

@[simp] lemma conjPart_nil : conjPart [] = [] := rfl

@[simp] lemma conjPart_cons (s0 : ℕ) (s : List ℕ) :
    conjPart (s0 :: s) = incrFirstN (conjPart s) s0 := rfl

/-- Coq `is_part_conj`. -/
lemma isPart_conjPart {μ : List ℕ} (h : IsPart μ) : IsPart (conjPart μ) := by
  induction μ with
  | nil => simp
  | cons a s ih => exact (ih h.2).incrFirstN a

/-- Coq `sumn_conj_part`: conjugation preserves the size. -/
@[simp] lemma sum_conjPart (μ : List ℕ) : (conjPart μ).sum = μ.sum := by
  induction μ with
  | nil => simp
  | cons a s ih => simp [ih, Nat.add_comm]

/-- Coq `size_conj_part`. -/
lemma length_conjPart {μ : List ℕ} (h : IsPart μ) : (conjPart μ).length = μ.headD 0 := by
  induction μ with
  | nil => simp
  | cons a s ih =>
    have hhead : s.headD 0 ≤ a := by
      cases s with
      | nil => simp
      | cons b t => simpa using h.1
    aesop

/-- Coq `conj_nseq`. -/
lemma conjPart_replicate_one {n : ℕ} (hn : 0 < n) : conjPart (List.replicate n 1) = [n] := by
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [List.replicate_succ, conjPart_cons, ih hm]
      simp

/-- Coq `in_conj_part` / `conj_ltnE`: the diagram of the conjugate is the transpose
of the diagram. -/
lemma inShape_conjPart {μ : List ℕ} (h : IsPart μ) (r c : ℕ) :
    InShape μ (r, c) ↔ InShape (conjPart μ) (c, r) := by
  induction μ generalizing r c with
  | nil => simp [InShape]
  | cons a s ih =>
    have hs : IsPart s := h.2
    have hhead : s.headD 0 ≤ a := by
      cases s with
      | nil => simp
      | cons b t => simpa using h.1
    -- the value of the conjugate in column `c`
    have hval : (conjPart (a :: s)).getD c 0
        = (conjPart s).getD c 0 + (if c < a then 1 else 0) := by
      rw [conjPart_cons, getD_incrFirstN]
      split_ifs <;> omega
    -- if `c ≥ a` then column `c` of the conjugate of `s` is empty
    have hzero : ¬ c < a → (conjPart s).getD c 0 = 0 := by
      intro hca
      by_contra hne
      have h0 : InShape (conjPart s) (c, 0) := Nat.pos_of_ne_zero hne
      have := (ih hs 0 c).2 h0
      simp only [InShape] at this
      have : c < s.headD 0 := by
        cases s with
        | nil => simp at this
        | cons b t => simpa using this
      omega
    cases r with
    | zero =>
      simp only [InShape, hval, List.getD_cons_zero]
      refine ⟨fun hca ↦ by simp [hca], fun hpos ↦ by aesop⟩
    | succ k =>
      have hIH := ih hs k c
      simp only [InShape, hval, List.getD_cons_succ] at hIH ⊢
      by_cases hca : c < a
      · rw [ite_eq_left hca]; omega
      · rw [ite_eq_right hca, hzero hca]; aesop

/-- Coq `conj_leqE`. -/
lemma getD_le_conjPart_iff {μ : List ℕ} (h : IsPart μ) (i j : ℕ) :
    μ.getD i 0 ≤ j ↔ (conjPart μ).getD j 0 ≤ i := by
  have := inShape_conjPart h i j
  simp only [InShape] at this
  omega

/-- Coq `conj_partK`: conjugation is an involution on partitions. -/
lemma conjPart_conjPart {μ : List ℕ} (h : IsPart μ) : conjPart (conjPart μ) = μ := by
  refine IsPart.ext_getD (isPart_conjPart (isPart_conjPart h)) h fun j => ?_
  have key : ∀ i, i < (conjPart (conjPart μ)).getD j 0 ↔ i < μ.getD j 0 := by
    intro i
    have h1 := inShape_conjPart (isPart_conjPart h) i j
    have h2 := inShape_conjPart h j i
    simp only [InShape] at h1 h2
    exact h1.symm.trans h2.symm
  exact Nat.le_antisymm (Nat.not_lt.1 fun hc => absurd ((key _).1 hc) (lt_irrefl _))
    (Nat.not_lt.1 fun hc => absurd ((key _).2 hc) (lt_irrefl _))

end Young
