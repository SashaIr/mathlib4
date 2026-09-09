/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# Rotations of binary trees and the Tamari order

Following `theories/Combi/bintree.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we define the rotations of a binary
tree and the Tamari order, the reflexive transitive closure of the rotation relation.
Binary trees are Mathlib's `Tree Unit`.

As in the Coq development, the rotation at a node replaces `((a, b), r)` by `(a, (b, r))`;
it preserves the number of nodes and strictly increases the sum `Tree.rightSizesSum` of
the sizes of the right subtrees, which gives the antisymmetry of the Tamari order.  A tree
admits no rotation exactly when all its left subtrees are empty, that is when it is the
comb `Tree.combRight`, and this comb is the largest element; mirroring left and right
reverses the order, so the comb `Tree.combLeft`, whose right subtrees are all empty, is
the smallest element.

## Main definitions and results

* `Tree.rotations t` : the list of the rotations of `t` (Coq `rotations`).
* `Tree.TamariLE t u` : the Tamari order (Coq `<=T`), the reflexive transitive closure of
  the rotation relation.
* `Tree.tamariLE_antisymm` : it is a partial order (`Tree.tamariPartialOrder`).
* `Tree.numNodes_of_tamariLE` : comparable trees have the same number of nodes.
* `Tree.rotations_eq_nil_iff` : a tree has no rotation iff it is a right comb (Coq
  `rightcomb_rotationsE`).
* `Tree.tamariLE_combRight` and `Tree.combLeft_tamariLE` : the right comb is the largest
  element and the left comb the smallest one (Coq `topETamari` and `botETamari`).
* `Tree.tamariLE_flipTree_iff` : mirroring a binary tree reverses the Tamari order (Coq
  `rotations_flip`).
-/

namespace BinaryTree

open BinaryTree

/-! ### Rotations -/

/-- The list of the rotations of a binary tree: the rotation at the root, if the left
subtree is not a leaf, followed by the rotations inside the two subtrees (Coq
`rotations`). -/
def rotations : BinaryTree Unit → List (BinaryTree Unit)
  | .nil => []
  | .node _ l r =>
      (match l with
        | .nil => []
        | .node _ a b => [BinaryTree.node () a (BinaryTree.node () b r)]) ++
      ((rotations l).map (fun lr => BinaryTree.node () lr r) ++
        (rotations r).map (fun rr => BinaryTree.node () l rr))

@[simp] lemma rotations_nil : rotations .nil = [] := rfl

lemma rotations_node (l r : BinaryTree Unit) :
  rotations (BinaryTree.node () l r)
      = (match l with
          | .nil => []
          | .node _ a b => [BinaryTree.node () a (BinaryTree.node () b r)]) ++
        ((rotations l).map (fun lr => BinaryTree.node () lr r) ++
          (rotations r).map (fun rr => BinaryTree.node () l rr)) := rfl

/-- The sum, over the nodes of a binary tree, of the number of nodes of the right subtree
(Coq `sumn (right_sizes t)`). -/
def rightSizesSum : BinaryTree Unit → ℕ
  | .nil => 0
  | .node _ l r => r.numNodes + rightSizesSum l + rightSizesSum r

@[simp] lemma rightSizesSum_nil : rightSizesSum .nil = 0 := rfl

@[simp] lemma rightSizesSum_node (l r : BinaryTree Unit) :
  rightSizesSum (BinaryTree.node () l r) = r.numNodes + rightSizesSum l + rightSizesSum r := rfl

/-- A rotation preserves the number of nodes (Coq `size_rotations`). -/
theorem numNodes_of_mem_rotations {t t' : BinaryTree Unit} (h : t' ∈ rotations t) :
    t'.numNodes = t.numNodes := by
  induction t generalizing t' with
  | nil => simp at h
  | node a l r ihl ihr =>
    cases a
    rw [rotations_node] at h
    simp only [List.mem_append, List.mem_map] at h
    rcases h with h | h | h
    · match l, h with
      | .node b c d, h =>
        simp only [List.mem_singleton] at h
        subst h
        cases b
        simp only [BinaryTree.numNodes]
        omega
    · obtain ⟨lr, hlr, rfl⟩ := h
      simp [BinaryTree.numNodes, ihl hlr]
    · obtain ⟨rr, hrr, rfl⟩ := h
      simp [BinaryTree.numNodes, ihr hrr]

/-- A rotation strictly increases the sum of the sizes of the right subtrees (Coq
`sumn_right_sizes_gt`). -/
theorem rightSizesSum_lt_of_mem_rotations {t t' : BinaryTree Unit} (h : t' ∈ rotations t) :
    rightSizesSum t < rightSizesSum t' := by
  induction t generalizing t' with
  | nil => simp at h
  | node a l r ihl ihr =>
    cases a
    rw [rotations_node] at h
    simp only [List.mem_append, List.mem_map] at h
    rcases h with h | h | h
    · match l, h with
      | .node b c d, h =>
        simp only [List.mem_singleton] at h
        subst h
        cases b
        simp only [rightSizesSum_node, BinaryTree.numNodes]
        omega
    · obtain ⟨lr, hlr, rfl⟩ := h
      have := ihl hlr
      simp only [rightSizesSum_node]
      omega
    · obtain ⟨rr, hrr, rfl⟩ := h
      have hnum := numNodes_of_mem_rotations hrr
      have := ihr hrr
      simp only [rightSizesSum_node, hnum]
      omega

/-- A crude bound on the sum of the sizes of the right subtrees, used as a termination
measure. -/
lemma rightSizesSum_le_numNodes_sq (t : BinaryTree Unit) :
    rightSizesSum t ≤ t.numNodes * t.numNodes := by
  induction t with
  | nil => simp
  | node a l r ihl ihr =>
    cases a
    simp only [rightSizesSum_node, BinaryTree.numNodes]
    nlinarith [ihl, ihr, Nat.zero_le l.numNodes, Nat.zero_le r.numNodes]

/-! ### The Tamari order -/

/-- The Tamari order: `TamariLE t u` when `u` is obtained from `t` by a sequence of
rotations (Coq `<=T`). -/
def TamariLE (t u : BinaryTree Unit) : Prop :=
  Relation.ReflTransGen (fun a b => b ∈ rotations a) t u

lemma tamariLE_refl (t : BinaryTree Unit) : TamariLE t t := Relation.ReflTransGen.refl

lemma tamariLE_trans {t u v : BinaryTree Unit} (htu : TamariLE t u) (huv : TamariLE u v) :
    TamariLE t v := Relation.ReflTransGen.trans htu huv

lemma tamariLE_of_mem_rotations {t u : BinaryTree Unit} (h : u ∈ rotations t) : TamariLE t u :=
  Relation.ReflTransGen.single h

/-- Two comparable trees have the same number of nodes. -/
theorem numNodes_of_tamariLE {t u : BinaryTree Unit} (h : TamariLE t u) :
    u.numNodes = t.numNodes := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => rw [numNodes_of_mem_rotations hstep, ih]

/-- The sum of the sizes of the right subtrees increases along the Tamari order. -/
theorem rightSizesSum_le_of_tamariLE {t u : BinaryTree Unit} (h : TamariLE t u) :
    rightSizesSum t ≤ rightSizesSum u := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => exact le_trans ih (le_of_lt (rightSizesSum_lt_of_mem_rotations hstep))

/-- Two distinct comparable trees have distinct sums of the sizes of the right
subtrees. -/
theorem rightSizesSum_lt_of_tamariLE_of_ne {t u : BinaryTree Unit} (h : TamariLE t u)
    (hne : t ≠ u) : rightSizesSum t < rightSizesSum u := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.1 h with rfl | h
  · exact absurd rfl hne
  · clear hne
    induction h with
    | single hstep => exact rightSizesSum_lt_of_mem_rotations hstep
    | tail hv hstep ih =>
      exact lt_trans (ih hv.to_reflTransGen) (rightSizesSum_lt_of_mem_rotations hstep)

/-- **The Tamari order is antisymmetric**. -/
theorem tamariLE_antisymm {t u : BinaryTree Unit} (htu : TamariLE t u) (hut : TamariLE u t) :
    t = u := by
  by_contra hne
  have h1 := rightSizesSum_lt_of_tamariLE_of_ne htu hne
  have h2 := rightSizesSum_lt_of_tamariLE_of_ne hut (Ne.symm hne)
  omega

/-- The Tamari order is a partial order on binary trees. -/
@[instance_reducible]
def tamariPartialOrder : PartialOrder (BinaryTree Unit) where
  le := TamariLE
  le_refl := tamariLE_refl
  le_trans _ _ _ := tamariLE_trans
  le_antisymm _ _ := tamariLE_antisymm

/-! ### The two combs -/

/-- The comb with `n` nodes whose nodes all have an empty right subtree (Coq
`leftcomb`). -/
def combLeft : ℕ → BinaryTree Unit
  | 0 => .nil
  | n + 1 => BinaryTree.node () (combLeft n) .nil

/-- The comb with `n` nodes whose nodes all have an empty left subtree (Coq
`rightcomb`). -/
def combRight : ℕ → BinaryTree Unit
  | 0 => .nil
  | n + 1 => BinaryTree.node () .nil (combRight n)

@[simp] lemma numNodes_combLeft (n : ℕ) : (combLeft n).numNodes = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [combLeft, BinaryTree.numNodes, ih]

@[simp] lemma numNodes_combRight (n : ℕ) : (combRight n).numNodes = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [combRight, BinaryTree.numNodes, ih]

@[simp] lemma rotations_combRight (n : ℕ) : rotations (combRight n) = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [combRight, rotations_node, ih]

/-- A tree admits no rotation exactly when it is a right comb (Coq
`rightcomb_rotationsE`). -/
theorem rotations_eq_nil_iff {t : BinaryTree Unit} : rotations t = [] ↔
    t = combRight t.numNodes := by
  constructor
  · intro h
    induction t with
    | nil => rfl
    | node a l r ihl ihr =>
      cases a
      rw [rotations_node] at h
      have hnil : ∀ s : List (BinaryTree Unit), ∀ u :
          List (BinaryTree Unit), s ++ u = [] → s = [] ∧ u = [] :=
        fun s u hsu => List.append_eq_nil_iff.1 hsu
      obtain ⟨hroot, hrest⟩ := hnil _ _ h
      obtain ⟨hl, hr⟩ := hnil _ _ hrest
      have hlnil : l = .nil := by
        match l with
        | .nil => rfl
        | .node b c d => simp at hroot
      subst hlnil
      have hrrot : rotations r = [] := by
        simpa using hr
      have hrcomb : r = combRight r.numNodes := ihr hrrot
      rw [BinaryTree.numNodes]
      simp only [combRight]
      rw [BinaryTree.numNodes]
      simpa using hrcomb
  · intro h
    rw [h]
    exact rotations_combRight _

/-- **The right comb is the largest element** of the Tamari order among the trees with a
given number of nodes (Coq `topETamari`). -/
theorem tamariLE_combRight (t : BinaryTree Unit) : TamariLE t (combRight t.numNodes) := by
  generalize hw : t.numNodes * t.numNodes - rightSizesSum t = w
  induction w using Nat.strong_induction_on generalizing t with
  | _ w ih =>
    by_cases hrot : rotations t = []
    · nth_rewrite 1 [rotations_eq_nil_iff.1 hrot]
      exact tamariLE_refl _
    · obtain ⟨t', ht'⟩ := List.exists_mem_of_ne_nil _ hrot
      have hnum := numNodes_of_mem_rotations ht'
      have hlt := rightSizesSum_lt_of_mem_rotations ht'
      have hbound := rightSizesSum_le_numNodes_sq t'
      rw [hnum] at hbound
      have hmeas : t'.numNodes * t'.numNodes - rightSizesSum t' < w := by
        rw [hnum, ← hw]
        omega
      have := ih _ hmeas t' rfl
      rw [hnum] at this
      exact tamariLE_trans (tamariLE_of_mem_rotations ht') this

/-! ### Mirror symmetry -/

/-- The mirror image of a binary tree, exchanging left and right (Coq `flip`). -/
def flipTree : BinaryTree Unit → BinaryTree Unit
  | .nil => .nil
  | .node _ l r => BinaryTree.node () (flipTree r) (flipTree l)

@[simp] lemma flipTree_nil : flipTree .nil = .nil := rfl

@[simp] lemma flipTree_node (l r : BinaryTree Unit) :
  flipTree (BinaryTree.node () l r) = BinaryTree.node () (flipTree r) (flipTree l) := rfl

@[simp] lemma flipTree_flipTree (t : BinaryTree Unit) : flipTree (flipTree t) = t := by
  induction t with
  | nil => rfl
  | node a l r ihl ihr =>
    cases a
    simp [ihl, ihr]

@[simp] lemma numNodes_flipTree (t : BinaryTree Unit) : (flipTree t).numNodes = t.numNodes := by
  induction t with
  | nil => rfl
  | node a l r ihl ihr =>
    cases a
    simp only [flipTree_node, BinaryTree.numNodes, ihl, ihr]
    omega

@[simp] lemma flipTree_combLeft (n : ℕ) : flipTree (combLeft n) = combRight n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [combLeft, combRight, ih]

@[simp] lemma flipTree_combRight (n : ℕ) : flipTree (combRight n) = combLeft n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [combLeft, combRight, ih]

/-- Mirroring reverses the rotations (Coq `rotations_flip`). -/
theorem mem_rotations_flipTree {t t' : BinaryTree Unit} (h : t' ∈ rotations t) :
    flipTree t ∈ rotations (flipTree t') := by
  induction t generalizing t' with
  | nil => simp at h
  | node a l r ihl ihr =>
    cases a
    rw [rotations_node] at h
    simp only [List.mem_append, List.mem_map] at h
    rcases h with h | h | h
    · match l, h with
      | .node b c d, h =>
        simp only [List.mem_singleton] at h
        subst h
        cases b
        simp only [flipTree_node, rotations_node, List.mem_append, List.mem_singleton]
        exact Or.inl trivial
    · obtain ⟨lr, hlr, rfl⟩ := h
      have := ihl hlr
      simp only [flipTree_node, rotations_node, List.mem_append, List.mem_map]
      exact Or.inr (Or.inr ⟨flipTree l, this, rfl⟩)
    · obtain ⟨rr, hrr, rfl⟩ := h
      have := ihr hrr
      simp only [flipTree_node, rotations_node, List.mem_append, List.mem_map]
      exact Or.inr (Or.inl ⟨flipTree r, this, rfl⟩)

/-- Mirroring reverses the Tamari order. -/
theorem tamariLE_flipTree {t u : BinaryTree Unit} (h : TamariLE t u) :
    TamariLE (flipTree u) (flipTree t) := by
  induction h with
  | refl => exact tamariLE_refl _
  | tail _ hstep ih =>
    exact tamariLE_trans (tamariLE_of_mem_rotations (mem_rotations_flipTree hstep)) ih

/-- Mirroring reverses the Tamari order (Coq `Tamari_flip`). -/
theorem tamariLE_flipTree_iff {t u : BinaryTree Unit} :
    TamariLE (flipTree u) (flipTree t) ↔ TamariLE t u := by
  refine ⟨fun h => ?_, tamariLE_flipTree⟩
  simpa using tamariLE_flipTree h

/-- **The left comb is the smallest element** of the Tamari order among the trees with a
given number of nodes (Coq `botETamari`). -/
theorem combLeft_tamariLE (t : BinaryTree Unit) : TamariLE (combLeft t.numNodes) t := by
  have h := tamariLE_combRight (flipTree t)
  rw [numNodes_flipTree] at h
  have := tamariLE_flipTree h
  rwa [flipTree_flipTree, flipTree_combRight] at this

end BinaryTree
