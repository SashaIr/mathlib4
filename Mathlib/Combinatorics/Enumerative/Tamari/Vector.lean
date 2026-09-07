/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Data.List.GetD
import Mathlib.Combinatorics.Enumerative.Tamari.Basic

/-!
# Tamari vectors

Following `theories/Combi/bintree.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we encode a binary tree by the list
`List.rightSizes t` of the sizes of the right subtrees of its nodes, read in infix order.
The lists arising in this way are the *Tamari vectors*, characterised by the predicate
`List.IsTamariVector` (Coq `is_Tamari`).

## Main definitions and results

* `List.rightSizes t` : the vector of the sizes of the right subtrees of `t` (Coq
  `right_sizes`).
* `List.IsTamariVector v` : the recursive characterisation of the Tamari vectors (Coq
  `is_Tamari` and `TamariVector`).
* `List.isTamariVector_iff` : the two global conditions defining a Tamari vector, namely
  `v i + i < |v|` and the fact that the intervals `[i, i + v i]` are nested (Coq
  `TamariP`).
* `List.isTamariVector_rightSizes` : the vector of a binary tree is a Tamari vector (Coq
  `right_sizesP`).
-/

namespace List

open Tree

/-! ### The vector of the sizes of the right subtrees -/

/-- The list of the sizes of the right subtrees of the nodes of a binary tree, read in
infix order (Coq `right_sizes`). -/
def rightSizes : Tree Unit → List ℕ
  | .nil => []
  | .node _ l r => rightSizes l ++ r.numNodes :: rightSizes r

@[simp] lemma rightSizes_nil : rightSizes .nil = [] := rfl

@[simp] lemma rightSizes_node (l r : Tree Unit) :
    rightSizes (Tree.node () l r) = rightSizes l ++ r.numNodes :: rightSizes r := rfl

@[simp] lemma length_rightSizes (t : Tree Unit) : (rightSizes t).length = t.numNodes := by
  induction t with
  | nil => rfl
  | node a l r ihl ihr =>
    cases a
    simp only [rightSizes_node, List.length_append, List.length_cons, ihl, ihr,
      Tree.numNodes]
    omega

/-- The sum of the vector of a tree is the weight used for the Tamari order. -/
@[simp] lemma sum_rightSizes (t : Tree Unit) : (rightSizes t).sum = rightSizesSum t := by
  induction t with
  | nil => rfl
  | node a l r ihl ihr =>
    cases a
    simp only [rightSizes_node, List.sum_append, List.sum_cons, ihl, ihr,
      rightSizesSum_node]
    omega

@[simp] lemma rightSizes_combLeft (n : ℕ) : rightSizes (combLeft n) = List.replicate n 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [combLeft, rightSizes_node, ih]
    simp [List.replicate_succ', Tree.numNodes]

/-! ### Tamari vectors -/

/-- The recursive characterisation of the Tamari vectors: the head `v₀` is at most the
length of the tail, the tail is again a Tamari vector, and `v i + i < v₀` for all `i < v₀`
(Coq `is_Tamari`). -/
def IsTamariVector : List ℕ → Prop
  | [] => True
  | v0 :: v => v0 ≤ v.length ∧ IsTamariVector v ∧ ∀ i < v0, v.getD i 0 + i < v0

@[simp] lemma isTamariVector_nil : IsTamariVector [] := trivial

lemma isTamariVector_cons_iff {v0 : ℕ} {v : List ℕ} :
    IsTamariVector (v0 :: v)
      ↔ v0 ≤ v.length ∧ IsTamariVector v ∧ ∀ i < v0, v.getD i 0 + i < v0 := Iff.rfl

/-- **The global characterisation of the Tamari vectors** (Coq `TamariP`): the entries
satisfy `v i + i < |v|`, and the intervals `[i, i + v i]` are nested. -/
theorem isTamariVector_iff {v : List ℕ} :
    IsTamariVector v ↔
      (∀ i < v.length, v.getD i 0 + i < v.length) ∧
      (∀ i j, i < j → j ≤ v.getD i 0 + i → v.getD j 0 + j ≤ v.getD i 0 + i) := by
  induction v with
  | nil =>
    simp only [isTamariVector_nil, List.length_nil, true_iff]
    refine ⟨fun i hi => absurd hi (by omega), fun i j hij hj => ?_⟩
    simp only [List.getD_eq_getElem?_getD, List.getElem?_nil, Option.getD_none] at hj ⊢
    omega
  | cons v0 v ih =>
    rw [isTamariVector_cons_iff]
    constructor
    · rintro ⟨hv0, htail, hlt⟩
      obtain ⟨ih1, ih2⟩ := ih.1 htail
      constructor
      · intro i hi
        match i with
        | 0 =>
          simp only [List.getD_cons_zero, List.length_cons]
          omega
        | i + 1 =>
          simp only [List.getD_cons_succ, List.length_cons] at hi ⊢
          have := ih1 i (by omega)
          omega
      · intro i j hij hj
        match i, j with
        | 0, j + 1 =>
          simp only [List.getD_cons_zero, List.getD_cons_succ] at hj ⊢
          have := hlt j (by omega)
          omega
        | i + 1, j + 1 =>
          simp only [List.getD_cons_succ] at hj ⊢
          have := ih2 i j (by omega) (by omega)
          omega
    · rintro ⟨h1, h2⟩
      have hv0 : v0 ≤ v.length := by
        have := h1 0 (by simp)
        simp only [List.getD_cons_zero, List.length_cons] at this
        omega
      refine ⟨hv0, ih.2 ⟨fun i hi => ?_, fun i j hij hj => ?_⟩, fun i hi => ?_⟩
      · have := h1 (i + 1) (by simp; omega)
        simp only [List.getD_cons_succ, List.length_cons] at this
        omega
      · have := h2 (i + 1) (j + 1) (by omega)
          (by simp only [List.getD_cons_succ]; omega)
        simp only [List.getD_cons_succ] at this
        omega
      · have := h2 0 (i + 1) (by omega) (by simp; omega)
        simp only [List.getD_cons_zero, List.getD_cons_succ] at this
        omega

/-- **The vector of the sizes of the right subtrees of a binary tree is a Tamari vector**
(Coq `right_sizesP`). -/
theorem isTamariVector_rightSizes (t : Tree Unit) : IsTamariVector (rightSizes t) := by
  induction t with
  | nil => exact isTamariVector_nil
  | node a l r ihl ihr =>
    cases a
    rw [isTamariVector_iff] at ihl ihr ⊢
    obtain ⟨hl1, hl2⟩ := ihl
    obtain ⟨hr1, hr2⟩ := ihr
    set p := l.numNodes with hp
    set q := r.numNodes with hq
    have hlen : (rightSizes (Tree.node () l r)).length = p + 1 + q := by
      rw [length_rightSizes]
      change l.numNodes + r.numNodes + 1 = p + 1 + q
      omega
    have hget : ∀ i, (rightSizes (Tree.node () l r)).getD i 0
        = if i < p then (rightSizes l).getD i 0
          else if i = p then q else (rightSizes r).getD (i - p - 1) 0 := by
      intro i
      rw [rightSizes_node]
      by_cases hip : i < p
      · rw [List.getD_append _ _ _ _ (by simpa [hp] using hip), ite_eq_left hip]
      · rw [List.getD_append_right _ _ _ _ (by simpa [hp] using Nat.le_of_not_lt hip),
          ite_eq_right hip]
        by_cases hie : i = p
        · rw [ite_eq_left hie]
          have hz : i - (rightSizes l).length = 0 := by
            rw [length_rightSizes]
            omega
          rw [hz, List.getD_cons_zero]
        · rw [ite_eq_right hie]
          have hsub : i - (rightSizes l).length = (i - p - 1) + 1 := by
            simp only [length_rightSizes, ← hp]
            omega
          rw [hsub, List.getD_cons_succ]
    have hl1' : ∀ i < p, (rightSizes l).getD i 0 + i < p := by
      intro i hi
      have := hl1 i (by simpa [hp] using hi)
      simpa [hp] using this
    have hr1' : ∀ i < q, (rightSizes r).getD i 0 + i < q := by
      intro i hi
      have := hr1 i (by simpa [hq] using hi)
      simpa [hq] using this
    constructor
    · intro i hi
      rw [hlen] at hi ⊢
      rw [hget i]
      by_cases hip : i < p
      · rw [ite_eq_left hip]
        have := hl1' i hip
        omega
      · rw [ite_eq_right hip]
        by_cases hie : i = p
        · rw [ite_eq_left hie]
          omega
        · rw [ite_eq_right hie]
          have := hr1' (i - p - 1) (by omega)
          omega
    · intro i j hij hj
      rw [hget i] at hj ⊢
      rw [hget j]
      by_cases hip : i < p
      · rw [ite_eq_left hip] at hj ⊢
        have hli := hl1' i hip
        have hjp : j < p := by omega
        rw [ite_eq_left hjp]
        exact hl2 i j hij hj
      · rw [ite_eq_right hip] at hj ⊢
        by_cases hie : i = p
        · rw [ite_eq_left hie] at hj ⊢
          have hjp : ¬ j < p := by omega
          rw [ite_eq_right hjp, ite_eq_right (by omega : j ≠ p)]
          have := hr1' (j - p - 1) (by omega)
          omega
        · rw [ite_eq_right hie] at hj ⊢
          have hip' : p < i := by omega
          have hjp : ¬ j < p := by omega
          rw [ite_eq_right hjp, ite_eq_right (by omega : j ≠ p)]
          have := hr2 (i - p - 1) (j - p - 1) (by omega) (by omega)
          omega

end List
