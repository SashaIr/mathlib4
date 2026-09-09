/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Combinatorics.Young.Shape.Basic
public import Mathlib.Tactic.Ring

/-!
# Integer compositions

A Lean 4 port of part of `theories/Combi/composition.v` from
[Coq-Combi](https://github.com/math-comp/Coq-Combi).

A *composition* of an integer `n` is a list of positive integers of sum `n`.
We enumerate the compositions of `n` and prove that there are exactly `2 ^ (n - 1)`
of them (Coq `card_intcompn`).

## Main definitions

* `List.IsComp s` : `s` has no zero part (Coq `is_comp`).
* `List.enumCompn n` : the list of all compositions of `n` (Coq `enum_compn`).
* `List.compnFinset n` : the finite set of all compositions of `n`.

## Main results

* `List.mem_enumCompn` : `enumCompn n` enumerates exactly the compositions of `n`.
* `List.nodup_enumCompn` : this enumeration has no repetition.
* `List.card_compnFinset`, `List.card_composition` : there are `2 ^ (n - 1)`
  compositions of `n` (Coq `card_intcompn`).
-/

@[expose] public section

namespace List

open List

/-- A shape is a composition when it has no zero part (Coq `is_comp`). -/
def IsComp (s : List ℕ) : Prop := 0 ∉ s

instance (s : List ℕ) : Decidable (IsComp s) := inferInstanceAs (Decidable (¬ _))

@[simp] lemma isComp_nil : IsComp [] := by simp [IsComp]

@[simp] lemma isComp_cons {a : ℕ} {s : List ℕ} : IsComp (a :: s) ↔ a ≠ 0 ∧ IsComp s := by
  simp [IsComp, eq_comm]

/-- Coq `part_is_comp`: a partition is a composition. -/
lemma IsPart.isComp {s : List ℕ} (h : IsPart s) : IsComp s := h.zero_notMem

/-- Coq `comp0`: the only composition of `0` is the empty one. -/
lemma eq_nil_of_isComp_of_sum_eq_zero {s : List ℕ} (hc : IsComp s) (hs : s.sum = 0) : s = [] := by
  cases s with
  | nil => rfl
  | cons a t =>
    rw [isComp_cons] at hc
    simp only [List.sum_cons] at hs
    omega

/-- Coq `size_comp`: a composition of `n` has at most `n` parts. -/
lemma length_le_sum_of_isComp {s : List ℕ} (hc : IsComp s) : s.length ≤ s.sum := by
  induction s with
  | nil => simp
  | cons a t ih =>
    rw [isComp_cons] at hc
    have := ih hc.2
    simp only [List.length_cons, List.sum_cons]
    omega

/-! ### Enumeration of the compositions of `n` -/

/-- The list of all compositions of `n` (Coq `enum_compn`). -/
def enumCompn : ℕ → List (List ℕ)
  | 0 => [[]]
  | (n + 1) => (List.range (n + 1)).flatMap fun i => (enumCompn (n - i)).map fun c => (i + 1) :: c
  decreasing_by omega

@[simp] lemma enumCompn_zero : enumCompn 0 = [[]] := by rw [enumCompn]

lemma enumCompn_succ (n : ℕ) :
    enumCompn (n + 1) =
      (List.range (n + 1)).flatMap fun i => (enumCompn (n - i)).map fun c => (i + 1) :: c := by
  rw [enumCompn]

/-- `enumCompn n` enumerates exactly the compositions of `n`. -/
lemma mem_enumCompn : ∀ (n : ℕ) (c : List ℕ), c ∈ enumCompn n ↔ IsComp c ∧ c.sum = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      intro c
      simp only [enumCompn_zero, List.mem_singleton]
      constructor
      · rintro rfl; simp
      · rintro ⟨hc, hs⟩; exact eq_nil_of_isComp_of_sum_eq_zero hc hs
    | (m + 1) =>
      intro c
      rw [enumCompn_succ, List.mem_flatMap]
      constructor
      · rintro ⟨i, hi, hmem⟩
        rw [List.mem_map] at hmem
        obtain ⟨d, hd, rfl⟩ := hmem
        rw [List.mem_range] at hi
        rw [ih (m - i) (by omega) d] at hd
        refine ⟨by simp [hd.1], ?_⟩
        simp only [List.sum_cons, hd.2]
        omega
      · rintro ⟨hc, hs⟩
        cases c with
        | nil => simp at hs
        | cons a t =>
          rw [isComp_cons] at hc
          simp only [List.sum_cons] at hs
          refine ⟨a - 1, List.mem_range.2 (by omega), ?_⟩
          rw [List.mem_map]
          refine ⟨t, ?_, by congr 1; omega⟩
          rw [ih (m - (a - 1)) (by omega) t]
          exact ⟨hc.2, by omega⟩

lemma nodup_enumCompn : ∀ n : ℕ, (enumCompn n).Nodup := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp
    | (m + 1) =>
      rw [enumCompn_succ, List.nodup_flatMap]
      constructor
      · intro i hi
        rw [List.mem_range] at hi
        exact (ih (m - i) (by omega)).map (fun _ _ h => (List.cons.injEq _ _ _ _ ▸ h).2)
      · refine List.Pairwise.imp ?_ (List.nodup_range (n := m + 1))
        intro i j hij c hci hcj
        rw [List.mem_map] at hci hcj
        obtain ⟨d, -, rfl⟩ := hci
        obtain ⟨e, -, he⟩ := hcj
        have h1 : i + 1 = j + 1 := (List.cons.injEq _ _ _ _ ▸ he.symm).1
        exact hij (by omega)

private lemma sum_range_two_pow_pred (n : ℕ) : ∑ k ∈ Finset.range (n + 1), 2 ^ (k - 1) = 2 ^ n := by
  induction n with
  | zero => simp
  | succ m ihm =>
    rw [Finset.sum_range_succ, ihm]
    simp only [Nat.add_sub_cancel]
    ring

private lemma sum_list_range (m : ℕ) (f : ℕ → ℕ) :
    ((List.range m).map f).sum = ∑ i ∈ Finset.range m, f i := by
  induction m with
  | zero => simp
  | succ k ihk =>
    rw [List.range_succ, List.map_append, List.sum_append, ihk,
      Finset.sum_range_succ, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

/-- There are `2 ^ (n - 1)` compositions of `n` (Coq `card_intcompn`). -/
lemma length_enumCompn : ∀ n : ℕ, (enumCompn n).length = 2 ^ (n - 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp
    | (m + 1) =>
      rw [enumCompn_succ, List.length_flatMap]
      have hmap : ((List.range (m + 1)).map
          fun i => ((enumCompn (m - i)).map fun c => (i + 1) :: c).length)
          = (List.range (m + 1)).map fun i => 2 ^ ((m - i) - 1) := by
        refine List.map_congr_left fun i hi => ?_
        rw [List.mem_range] at hi
        rw [List.length_map, ih (m - i) (by omega)]
      rw [hmap, sum_list_range]
      have hrefl : ∑ i ∈ Finset.range (m + 1), 2 ^ ((m - i) - 1)
          = ∑ k ∈ Finset.range (m + 1), 2 ^ (k - 1) := by
        rw [← Finset.sum_range_reflect]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.mem_range] at hi
        congr 2
        omega
      rw [hrefl, sum_range_two_pow_pred]
      simp

/-! ### The finite set of compositions of `n` -/

/-- The finite set of all compositions of `n`. -/
def compnFinset (n : ℕ) : Finset (List ℕ) := (enumCompn n).toFinset

@[simp] lemma mem_compnFinset {n : ℕ} {c : List ℕ} :
    c ∈ compnFinset n ↔ IsComp c ∧ c.sum = n := by
  rw [compnFinset, List.mem_toFinset, mem_enumCompn]

lemma card_compnFinset (n : ℕ) : (compnFinset n).card = 2 ^ (n - 1) := by
  rw [compnFinset, List.toFinset_card_of_nodup (nodup_enumCompn n), length_enumCompn]

instance fintypeComposition (n : ℕ) : Fintype {c : List ℕ // IsComp c ∧ c.sum = n} :=
  Fintype.subtype (compnFinset n) fun _ => mem_compnFinset

/-- Coq `card_intcompn`: the number of compositions of `n` is `2 ^ (n - 1)`. -/
theorem card_composition (n : ℕ) :
    Fintype.card {c : List ℕ // IsComp c ∧ c.sum = n} = 2 ^ (n - 1) := by
  rw [Fintype.card_of_subtype (compnFinset n) fun _ => mem_compnFinset, card_compnFinset]

end List
