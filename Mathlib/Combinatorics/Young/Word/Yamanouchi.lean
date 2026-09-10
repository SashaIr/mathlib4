/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Combinatorics.Young.Shape.Corners

/-!
# Yamanouchi words

A Lean 4 port of `theories/Combi/Yamanouchi.v` from
[Coq-Combi](https://github.com/math-comp/Coq-Combi).

A *Yamanouchi word* is a list of naturals such that in every suffix, each letter
`i + 1` occurs at most as often as the letter `i`.  Yamanouchi words are in
bijection with standard Young tableaux; here we develop their basic theory: the
evaluation of a word, the characterisation by counts in suffixes, the operation
removing the zeroes, and the hyperstandard Yamanouchi word of a given evaluation.

## Main definitions

* `Young.evalseq s` : the evaluation of `s`, the list of the numbers of occurrences
  of `0, 1, 2, ...` in `s` (Coq `evalseq`).
* `Young.IsYam s` : `s` is a Yamanouchi word (Coq `is_yam`).
* `Young.decrYam s` : remove the zeroes of `s` and decrease all other letters
  (Coq `decr_yam`).
* `Young.hyperYam ev` : the hyperstandard Yamanouchi word `... 2222 11111 0000000`
  of evaluation `ev` (Coq `hyper_yam`).

## Main results

* `Young.getD_evalseq` : the `i`-th entry of `evalseq s` is the number of `i` in `s`.
* `Young.isYam_iff_count` (Coq `is_yamP`) : characterisation of Yamanouchi words.
* `Young.IsYam.isPart_evalseq` : the evaluation of a Yamanouchi word is a partition.
* `Young.evalseq_hyperYam`, `Young.isYam_hyperYam` : for any partition `ev` there is
  a Yamanouchi word of evaluation `ev`.
-/

@[expose] public section

namespace Young

open List

/-! ### Evaluation of a word -/

/-- The evaluation of a word: the list whose `i`-th entry is the number of
occurrences of `i` (Coq `evalseq`). -/
def evalseq : List ℕ → List ℕ
  | [] => []
  | s0 :: s => incrNth (evalseq s) s0

@[simp] lemma evalseq_nil : evalseq [] = [] := rfl

@[simp] lemma evalseq_cons (s0 : ℕ) (s : List ℕ) :
    evalseq (s0 :: s) = incrNth (evalseq s) s0 := rfl

/-- Coq `nth_evalseq`. -/
lemma getD_evalseq (s : List ℕ) (i : ℕ) : (evalseq s).getD i 0 = s.count i := by
  induction s with
  | nil => simp
  | cons a s ih =>
    rw [evalseq_cons, getD_incrNth, ih, List.count_cons]
    simp only [beq_iff_eq]

/-- Coq `evalseq_eq_size`. -/
@[simp] lemma sum_evalseq (s : List ℕ) : (evalseq s).sum = s.length := by
  induction s with
  | nil => simp
  | cons a s ih => simp [ih]

lemma getLastD_incrNth_ne_zero {l : List ℕ} (hl : l.getLastD 1 ≠ 0) (i : ℕ) :
    (incrNth l i).getLastD 1 ≠ 0 := by
  have hlen : (incrNth l i).length = max l.length (i + 1) := length_incrNth l i
  have hne : incrNth l i ≠ [] := by
    intro hc
    rw [hc] at hlen
    simp at hlen
    omega
  rw [getLastD_eq_getD hne, getD_incrNth, hlen]
  rcases Nat.lt_or_ge (i + 1) l.length with h | h
  · have hmax : max l.length (i + 1) = l.length := by omega
    rw [hmax, ite_eq_right (by omega)]
    have hlne : l ≠ [] := by
      intro hc
      rw [hc] at h
      simp at h
    rw [← getLastD_eq_getD hlne]
    simpa using hl
  · have hmax : max l.length (i + 1) = i + 1 := by omega
    rw [hmax]
    simp

/-- The evaluation of a word never ends with a zero. -/
lemma getLastD_evalseq_ne_zero (s : List ℕ) : (evalseq s).getLastD 1 ≠ 0 := by
  induction s with
  | nil => simp
  | cons a s ih => exact getLastD_incrNth_ne_zero ih a

/-- Coq `evalseq0`. -/
lemma eq_nil_of_evalseq_eq_nil {s : List ℕ} (h : evalseq s = []) : s = [] := by
  have := sum_evalseq s
  rw [h] at this
  simpa using (List.length_eq_zero_iff.1 this.symm)

/-! ### Yamanouchi words -/

/-- `IsYam s` : `s` is a Yamanouchi word (Coq `is_yam`). -/
def IsYam : List ℕ → Prop
  | [] => True
  | s0 :: s => IsPart (evalseq (s0 :: s)) ∧ IsYam s

@[simp] lemma isYam_nil : IsYam [] := trivial

@[simp] lemma isYam_cons {s0 : ℕ} {s : List ℕ} :
    IsYam (s0 :: s) ↔ IsPart (evalseq (s0 :: s)) ∧ IsYam s := Iff.rfl

lemma IsYam.of_cons {s0 : ℕ} {s : List ℕ} (h : IsYam (s0 :: s)) : IsYam s := h.2

/-- Coq `is_part_eval_yam`. -/
lemma IsYam.isPart_evalseq {s : List ℕ} (h : IsYam s) : IsPart (evalseq s) := by
  cases s with
  | nil => simp
  | cons a s => exact h.1

/-- Coq `is_yamP`: a word is Yamanouchi iff in each of its suffixes, every letter
occurs at least as often as its successor. -/
lemma isYam_iff_count {s : List ℕ} :
    IsYam s ↔ ∀ i n, (s.drop i).count (n + 1) ≤ (s.drop i).count n := by
  constructor
  · intro h i n
    induction s generalizing i with
    | nil => simp
    | cons a s ih =>
      cases i with
      | zero =>
        have := h.1.getD_succ_le n
        rw [getD_evalseq, getD_evalseq] at this
        simpa using this
      | succ j => simpa using ih h.2 j
  · intro h
    induction s with
    | nil => simp
    | cons a s ih =>
      refine ⟨?_, ih fun i n => by simpa using h (i + 1) n⟩
      refine isPart_of_getD (getLastD_evalseq_ne_zero _) fun n => ?_
      rw [getD_evalseq, getD_evalseq]
      simpa using h 0 n

/-- Coq `last_yam`: a Yamanouchi word ends with a zero. -/
lemma IsYam.getLastD_eq_zero {y : List ℕ} (h : IsYam y) : y.getLastD 0 = 0 := by
  rcases List.eq_nil_or_concat y with rfl | ⟨z, a, rfl⟩
  · simp
  · simp only [List.concat_eq_append] at h ⊢
    rw [List.getLastD_concat]
    by_contra ha
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    have hdrop : (z ++ [b + 1]).drop z.length = [b + 1] := by simp
    have := (isYam_iff_count.1 h) z.length b
    rw [hdrop] at this
    simp at this

/-! ### Removing the zeroes -/

/-- Remove the zeroes of a word and decrease all its other letters (Coq `decr_yam`). -/
def decrYam : List ℕ → List ℕ
  | [] => []
  | 0 :: s => decrYam s
  | (n + 1) :: s => n :: decrYam s

@[simp] lemma decrYam_nil : decrYam [] = [] := rfl

@[simp] lemma decrYam_zero_cons (s : List ℕ) : decrYam (0 :: s) = decrYam s := rfl

@[simp] lemma decrYam_succ_cons (n : ℕ) (s : List ℕ) :
    decrYam ((n + 1) :: s) = n :: decrYam s := rfl

lemma count_decrYam (s : List ℕ) (i : ℕ) : (decrYam s).count i = s.count (i + 1) := by
  induction s with
  | nil => simp
  | cons a s ih =>
    cases a with
    | zero => simp [ih]
    | succ n =>
      simp only [decrYam_succ_cons, List.count_cons, ih, beq_iff_eq, Nat.add_right_cancel_iff]

lemma getLastD_tail_ne_zero {l : List ℕ} (h : l.getLastD 1 ≠ 0) :
    l.tail.getLastD 1 ≠ 0 := by
  cases l with
  | nil => simp
  | cons a t =>
    rw [List.tail_cons]
    cases t with
    | nil => simp
    | cons b u =>
      rw [List.getLastD_cons, getLastD_eq_getD (d' := 0) (by simp)] at h
      rw [getLastD_eq_getD (d' := 0) (by simp)]
      exact h

/-- Coq `evalseq_decr_yam`. -/
lemma evalseq_decrYam (s : List ℕ) : evalseq (decrYam s) = (evalseq s).tail := by
  refine ext_getD_of_getLastD_ne_zero (getLastD_evalseq_ne_zero _)
    (getLastD_tail_ne_zero (getLastD_evalseq_ne_zero s)) fun i => ?_
  rw [getD_evalseq, count_decrYam, getD_tail, getD_evalseq]

/-- Every suffix of `decrYam s` is `decrYam` of a suffix of `s`. -/
lemma exists_drop_decrYam (s : List ℕ) (i : ℕ) : ∃ j, (decrYam s).drop i = decrYam (s.drop j) := by
  induction s generalizing i with
  | nil => exact ⟨0, by simp⟩
  | cons a s ih =>
    cases a with
    | zero =>
      obtain ⟨j, hj⟩ := ih i
      exact ⟨j + 1, by simpa using hj⟩
    | succ n =>
      cases i with
      | zero => exact ⟨0, by simp⟩
      | succ k =>
        obtain ⟨j, hj⟩ := ih k
        exact ⟨j + 1, by simpa using hj⟩

/-- Coq `is_yam_decr`. -/
lemma isYam_decrYam {s : List ℕ} (h : IsYam s) : IsYam (decrYam s) := by
  rw [isYam_iff_count]
  intro i n
  obtain ⟨j, hj⟩ := exists_drop_decrYam s i
  rw [hj, count_decrYam, count_decrYam]
  exact (isYam_iff_count.1 h) j (n + 1)

/-! ### Corners of the evaluation -/

/-- Coq `is_rem_corner_yam`. -/
lemma isRemCorner_evalseq {l0 : ℕ} {s : List ℕ} (h : IsYam (l0 :: s)) :
    IsRemCorner (evalseq (l0 :: s)) l0 :=
  isRemCorner_incrNth h.2.isPart_evalseq

/-- Coq `is_add_corner_yam`. -/
lemma isAddCorner_evalseq {l0 : ℕ} {s : List ℕ} (h : IsYam (l0 :: s)) :
    IsAddCorner (evalseq s) l0 := by
  rcases Nat.eq_zero_or_pos l0 with rfl | hl0
  · exact Or.inl rfl
  refine Or.inr ?_
  have hmono := h.1.getD_antitone (i := l0 - 1) (j := l0) (by omega)
  rw [evalseq_cons, getD_incrNth, getD_incrNth, ite_eq_left rfl,
    ite_eq_right (by omega : ¬ (l0 = l0 - 1))] at hmono
  omega

/-! ### The hyperstandard Yamanouchi word -/

/-- Auxiliary definition for `hyperYam` (Coq `hyper_yam_rev`). -/
def hyperYamRev : List ℕ → List ℕ
  | [] => []
  | s0 :: s => List.replicate s0 s.length ++ hyperYamRev s

/-- The hyperstandard Yamanouchi word of evaluation `ev`, of the shape
`... 2222 11111 0000000` (Coq `hyper_yam`). -/
def hyperYam (ev : List ℕ) : List ℕ := hyperYamRev ev.reverse

@[simp] lemma hyperYamRev_nil : hyperYamRev [] = [] := rfl

@[simp] lemma hyperYamRev_cons (s0 : ℕ) (s : List ℕ) :
    hyperYamRev (s0 :: s) = List.replicate s0 s.length ++ hyperYamRev s := rfl

@[simp] lemma hyperYam_nil : hyperYam [] = [] := rfl

lemma length_hyperYamRev (l : List ℕ) : (hyperYamRev l).length = l.sum := by
  induction l with
  | nil => simp
  | cons a s ih => simp [ih]

/-- Coq `size_hyper_yam`. -/
lemma length_hyperYam (ev : List ℕ) : (hyperYam ev).length = ev.sum := by
  rw [hyperYam, length_hyperYamRev, List.sum_reverse]

lemma count_hyperYamRev (l : List ℕ) (i : ℕ) :
    (hyperYamRev l).count i = if i < l.length then l.getD (l.length - 1 - i) 0 else 0 := by
  induction l with
  | nil => simp
  | cons a s ih =>
    rw [hyperYamRev_cons, List.count_append, List.count_replicate, ih]
    grind

lemma count_hyperYam (ev : List ℕ) (i : ℕ) : (hyperYam ev).count i = ev.getD i 0 := by
  rw [hyperYam, count_hyperYamRev]
  by_cases hi : i < ev.reverse.length
  · rw [ite_eq_left hi]
    simp only [List.length_reverse] at hi ⊢
    rw [List.getD_reverse _ (by omega)]
    congr 1
    omega
  · rw [ite_eq_right hi]
    simp only [List.length_reverse] at hi
    exact (List.getD_eq_default _ _ (by omega)).symm

/-- Coq `evalseq_hyper_yam`. -/
lemma evalseq_hyperYam {ev : List ℕ} (h : IsPart ev) : evalseq (hyperYam ev) = ev := by
  refine ext_getD_of_getLastD_ne_zero (getLastD_evalseq_ne_zero _) h.getLastD_ne_zero fun i => ?_
  rw [getD_evalseq, count_hyperYam]

/-- Splitting off the first block of letters of `hyperYamRev`. -/
lemma count_drop_hyperYamRev_cons (a : ℕ) (s : List ℕ) (i m : ℕ) :
    ((hyperYamRev (a :: s)).drop i).count m
      = (if m = s.length then a - i else 0) + ((hyperYamRev s).drop (i - a)).count m := by
  rw [hyperYamRev_cons, List.drop_append, List.count_append, List.drop_replicate,
    List.count_replicate, List.length_replicate]
  congr 1
  by_cases hm : m = s.length
  · simp [hm]
  · rw [ite_eq_right hm, ite_eq_right (by simpa using fun hc => hm hc.symm)]

/-- The key inequality: in every suffix of `hyperYamRev l`, where `l` is weakly increasing,
each letter occurs at least as often as its successor. -/
lemma count_drop_hyperYamRev_le (l : List ℕ)
    (H : ∀ j, j + 1 < l.length → l.getD j 0 ≤ l.getD (j + 1) 0) (i n : ℕ) :
    ((hyperYamRev l).drop i).count (n + 1) ≤ ((hyperYamRev l).drop i).count n := by
  induction l generalizing i n with
  | nil => simp
  | cons a s ih =>
    have Hs : ∀ j, j + 1 < s.length → s.getD j 0 ≤ s.getD (j + 1) 0 := by
      intro j hj
      have := H (j + 1) (by simp; omega)
      simpa using this
    rw [count_drop_hyperYamRev_cons, count_drop_hyperYamRev_cons]
    by_cases hn : n + 1 = s.length
    · rw [ite_eq_left hn, ite_eq_right (by omega)]
      have hzero : ((hyperYamRev s).drop (i - a)).count (n + 1) = 0 := by
        have hsub : ((hyperYamRev s).drop (i - a)).count (n + 1)
            ≤ (hyperYamRev s).count (n + 1) :=
          (List.drop_sublist _ _).count_le _
        rw [count_hyperYamRev, ite_eq_right (by omega)] at hsub
        omega
      cases s with
      | nil => simp at hn
      | cons s0 t =>
        have hn' : n = t.length := by simpa using hn
        have ha : a ≤ s0 := by
          have := H 0 (by simp)
          simpa using this
        have hkey : a - i ≤ ((hyperYamRev (s0 :: t)).drop (i - a)).count n := by
          rw [count_drop_hyperYamRev_cons, ite_eq_left hn']
          omega
        omega
    · rw [ite_eq_right hn]
      have := ih Hs (i - a) n
      split_ifs <;> omega

/-- Coq `hyper_yamP`: the hyperstandard word of a partition is a Yamanouchi word. -/
lemma isYam_hyperYam {ev : List ℕ} (h : IsPart ev) : IsYam (hyperYam ev) := by
  rw [isYam_iff_count]
  intro i n
  rw [hyperYam]
  refine count_drop_hyperYamRev_le _ (fun j hj => ?_) i n
  simp only [List.length_reverse] at hj
  rw [List.getD_reverse _ (by omega), List.getD_reverse _ (by omega)]
  exact h.getD_antitone (by omega)

end Young
