/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Enumerative.Catalan.Tree
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Ordered trees

This file ports `theories/Combi/ordtree.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi).  An *ordered tree* (also called a
plane tree) is a rooted tree in which every node carries a possibly empty ordered list of
subtrees.

The main result is the classical *rotation correspondence*: ordered trees with `n + 1`
nodes are in bijection with binary trees with `n` internal nodes, so that they are counted
by the Catalan number `catalan n`.  Binary trees are Mathlib's `Tree Unit`, as in
`Mathlib.Combinatorics.Enumerative.Tamari.Basic`.

## Main definitions

* `OrdTree` : the type of ordered trees.
* `OrdTree.toBin`, `OrdTree.ofBin` : the rotation correspondence between
  ordered trees and binary trees (Coq `ord_to_bintree` and `bin_to_ordtree`).
* `OrdTree.size`, `OrdTree.depth` : the number of nodes and the maximal number
  of nodes on a branch.
* `OrdTree.lineTree n` : the linear tree with `n + 1` nodes.

## Main results

* `OrdTree.equivBin` : the rotation correspondence is a bijection.
* `OrdTree.nat_card_size_eq` : there are `catalan n` ordered trees with `n + 1`
  nodes (Coq `card_ordtreesz`).
* `OrdTree.depth_le_size` and `OrdTree.depth_eq_size_iff` : the depth is at
  most the size, with equality exactly for the linear trees (Coq `depth_le_size`).
* `OrdTree.depth_eq_two_iff` : the trees of depth `2` are the "brooms" (Coq
  `depth_tree_eq2P`).
-/

@[expose] public section

/-- An **ordered tree** (or plane tree): a root together with an ordered list of ordered
trees, its subtrees (Coq `ordtree`). -/
inductive OrdTree where
  /-- The tree whose subtrees are the elements of the list `f` (Coq `OrdNode`). -/
  | node : List OrdTree → OrdTree

namespace OrdTree

/-- The constructor of ordered trees is injective. -/
lemma node_injective : Function.Injective node := by
  rintro f g h
  cases h
  rfl

/-- The induction principle for ordered trees: to prove a statement for every ordered
tree, it suffices to prove it for `node f` assuming it for all the elements of `f`. -/
@[elab_as_elim]
theorem rec_ind {P : OrdTree → Prop} (h : ∀ f : List OrdTree, (∀ t ∈ f, P t) → P (node f))
    (t : OrdTree) : P t :=
  OrdTree.rec (motive_2 := fun f => ∀ t ∈ f, P t) (fun f hf => h f hf)
    (fun _ hmem => absurd hmem List.not_mem_nil)
    (fun a l ha hl t ht => by
      rcases List.mem_cons.1 ht with rfl | ht
      · exact ha
      · exact hl t ht) t

/-! ### The rotation correspondence with binary trees -/

/-- The binary tree attached to an ordered tree by the rotation correspondence: the left
subtree encodes the first subtree, the right subtree the remaining ones (Coq
`ord_to_bintree`). -/
def toBin : OrdTree → BinaryTree Unit
  | node [] => .nil
  | node (t :: f) => .node () (toBin t) (toBin (node f))

@[simp] lemma toBin_nil : toBin (node []) = .nil := by rw [toBin]

@[simp] lemma toBin_cons (t : OrdTree) (f : List OrdTree) :
    toBin (node (t :: f)) = .node () (toBin t) (toBin (node f)) := by rw [toBin]

/-- The forest attached to a binary tree by the rotation correspondence (Coq
`bin_to_forest`). -/
def ofBinForest : BinaryTree Unit → List OrdTree
  | .nil => []
  | .node _ l r => node (ofBinForest l) :: ofBinForest r

@[simp] lemma ofBinForest_nil : ofBinForest .nil = [] := rfl

@[simp] lemma ofBinForest_node (l r : BinaryTree Unit) :
    ofBinForest (.node () l r) = node (ofBinForest l) :: ofBinForest r := rfl

/-- The ordered tree attached to a binary tree by the rotation correspondence (Coq
`bin_to_ordtree`). -/
def ofBin (t : BinaryTree Unit) : OrdTree := node (ofBinForest t)

@[simp] lemma toBin_ofBin (t : BinaryTree Unit) : toBin (ofBin t) = t := by
  induction t with
  | nil => rw [ofBin, ofBinForest_nil, toBin_nil]
  | node a l r ihl ihr =>
    cases a
    rw [ofBin, ofBinForest_node, toBin_cons]
    rw [ofBin] at ihl ihr
    rw [ihl, ihr]

/-- Auxiliary form of `OrdTree.ofBin_toBin` for a forest. -/
lemma ofBinForest_toBin_node : ∀ f : List OrdTree, (∀ t ∈ f, ofBin (toBin t) = t) →
    ofBinForest (toBin (node f)) = f
  | [], _ => by rw [toBin_nil, ofBinForest_nil]
  | a :: l, h => by
    rw [toBin_cons, ofBinForest_node,
      ofBinForest_toBin_node l fun t ht => h t (List.mem_cons_of_mem _ ht)]
    exact congrArg (· :: l) (h a List.mem_cons_self)

@[simp] lemma ofBin_toBin (t : OrdTree) : ofBin (toBin t) = t := by
  induction t using rec_ind with
  | _ f ih => exact congrArg node (ofBinForest_toBin_node f ih)


/-- The **rotation correspondence**: ordered trees are in bijection with binary trees. -/
def equivBin : OrdTree ≃ BinaryTree Unit where
  toFun := toBin
  invFun := ofBin
  left_inv := ofBin_toBin
  right_inv := toBin_ofBin


/-- Ordered trees have decidable equality, transported from binary trees along the
rotation correspondence. -/
instance : DecidableEq OrdTree := fun a b =>
  decidable_of_iff (toBin a = toBin b) equivBin.injective.eq_iff

/-! ### The number of nodes -/

/-- The number of nodes of an ordered tree (Coq `size_ordtree`). -/
def size : OrdTree → ℕ
  | node f => 1 + (f.map size).sum

@[simp] lemma size_node (f : List OrdTree) : (node f).size = 1 + (f.map size).sum := by
  rw [size]

/-- Peeling off the first subtree in the number of nodes. -/
lemma size_node_cons (t : OrdTree) (f : List OrdTree) :
    (node (t :: f)).size = t.size + (node f).size := by
  rw [size_node, size_node, List.map_cons, List.sum_cons]
  omega

/-- An ordered tree has at least one node. -/
lemma size_pos (t : OrdTree) : 0 < t.size := by
  cases t with
  | node f => rw [size_node]; omega

/-- The trees with a single node are the leaves. -/
lemma size_eq_one_iff {t : OrdTree} : t.size = 1 ↔ t = node [] := by
  cases t with
  | node f =>
    cases f with
    | nil => simp
    | cons a l =>
      have ha := size_pos a
      have hl := size_pos (node l)
      rw [size_node_cons]
      simp only [OrdTree.node.injEq, reduceCtorEq, iff_false]
      omega

/-- The rotation correspondence adds one node. -/
lemma size_ofBin (t : BinaryTree Unit) : (ofBin t).size = t.numNodes + 1 := by
  induction t with
  | nil => rw [ofBin, ofBinForest_nil, size_node]; simp
  | node a l r ihl ihr =>
    cases a
    rw [ofBin, ofBinForest_node, ← show ofBin l = node (ofBinForest l) from rfl,
      size_node_cons, ← show ofBin r = node (ofBinForest r) from rfl, ihl, ihr]
    simp [BinaryTree.numNodes]
    omega

/-- The number of nodes of an ordered tree exceeds by one the number of internal nodes of
the corresponding binary tree. -/
lemma size_eq_numNodes_toBin_add_one (t : OrdTree) : t.size = (toBin t).numNodes + 1 := by
  conv_lhs => rw [← ofBin_toBin t]
  rw [size_ofBin]

/-! ### Counting ordered trees -/

/-- The rotation correspondence restricted to the trees of a given size. -/
def sizeEquiv (n : ℕ) : {t : OrdTree // t.size = n + 1} ≃ {b : BinaryTree Unit // b.numNodes = n} :=
  equivBin.subtypeEquiv fun t => by
    change t.size = n + 1 ↔ (toBin t).numNodes = n
    rw [size_eq_numNodes_toBin_add_one]
    exact ⟨fun h => by omega, fun h => by rw [h]⟩

/-- **Ordered trees are counted by the Catalan numbers**: there are `catalan n` ordered
trees with `n + 1` nodes (Coq `card_ordtreesz`). -/
theorem nat_card_size_eq (n : ℕ) :
    Nat.card {t : OrdTree // t.size = n + 1} = catalan n := by
  rw [Nat.card_congr (sizeEquiv n),
    Nat.card_congr (Equiv.subtypeEquivRight fun b : BinaryTree Unit =>
      (BinaryTree.mem_treesOfNumNodesEq (x := b) (n := n)).symm),
    Nat.card_eq_fintype_card, Fintype.card_coe, BinaryTree.treesOfNumNodesEq_card_eq_catalan]

/-! ### The depth -/

/-- The depth of an ordered tree: the maximal number of nodes on a branch (Coq
`depth_ordtree`). -/
def depth : OrdTree → ℕ
  | node f => 1 + (f.map depth).foldr max 0

@[simp] lemma depth_node (f : List OrdTree) :
    (node f).depth = 1 + (f.map depth).foldr max 0 := by
  rw [depth]

/-- Peeling off the first subtree in the depth. -/
lemma depth_node_cons (t : OrdTree) (f : List OrdTree) :
    (node (t :: f)).depth = max (t.depth + 1) ((node f).depth) := by
  rw [depth_node, depth_node, List.map_cons, List.foldr_cons]
  omega

/-- An ordered tree has depth at least one. -/
lemma depth_pos (t : OrdTree) : 0 < t.depth := by
  cases t with
  | node f => rw [depth_node]; omega

/-- The trees of depth one are the leaves. -/
lemma depth_eq_one_iff {t : OrdTree} : t.depth = 1 ↔ t = node [] := by
  cases t with
  | node f =>
    cases f with
    | nil => simp
    | cons a l =>
      have ha := depth_pos a
      rw [depth_node_cons]
      simp only [OrdTree.node.injEq, reduceCtorEq, iff_false]
      omega

/-! ### Linear trees -/

/-- The linear ordered tree with `n + 1` nodes, each having at most one subtree (Coq
`line_ordtree`). -/
def lineTree : ℕ → OrdTree
  | 0 => node []
  | n + 1 => node [lineTree n]

@[simp] lemma size_lineTree (n : ℕ) : (lineTree n).size = n + 1 := by
  induction n with
  | zero => rw [lineTree, size_node]; simp
  | succ n ih => rw [lineTree, size_node_cons, ih, size_node]; simp

@[simp] lemma depth_lineTree (n : ℕ) : (lineTree n).depth = n + 1 := by
  induction n with
  | zero => rw [lineTree, depth_node]; simp
  | succ n ih => rw [lineTree, depth_node_cons, ih, depth_node]; simp

/-! ### Comparing the depth and the size -/

/-- Auxiliary form of `OrdTree.depth_le_size` for a forest. -/
lemma foldr_max_depth_le_sum_size : ∀ f : List OrdTree, (∀ t ∈ f, t.depth ≤ t.size) →
    (f.map depth).foldr max 0 ≤ (f.map size).sum
  | [], _ => by simp
  | a :: l, h => by
    have hl := foldr_max_depth_le_sum_size l fun t ht => h t (List.mem_cons_of_mem _ ht)
    have ha := h a List.mem_cons_self
    rw [List.map_cons, List.map_cons, List.foldr_cons, List.sum_cons]
    omega

/-- **The depth of an ordered tree is at most its size** (Coq `depth_le_size`). -/
theorem depth_le_size (t : OrdTree) : t.depth ≤ t.size := by
  induction t using rec_ind with
  | _ f ih =>
    rw [depth_node, size_node]
    have := foldr_max_depth_le_sum_size f ih
    omega

/-- A forest whose sizes sum to zero is empty. -/
lemma eq_nil_of_sum_size_eq_zero {f : List OrdTree} (h : (f.map size).sum = 0) : f = [] := by
  cases f with
  | nil => rfl
  | cons a l =>
    have := size_pos a
    rw [List.map_cons, List.sum_cons] at h
    omega

/-- **The trees whose depth equals their size are the linear trees** (Coq
`depth_le_size`). -/
theorem depth_eq_size_iff {t : OrdTree} : t.depth = t.size ↔ ∃ n, t = lineTree n := by
  constructor
  · induction t using rec_ind with
    | _ f ih =>
      intro heq
      rw [depth_node, size_node] at heq
      cases f with
      | nil => exact ⟨0, by rw [lineTree]⟩
      | cons a l =>
        have hal : (l.map depth).foldr max 0 ≤ (l.map size).sum :=
          foldr_max_depth_le_sum_size l fun t ht =>
            depth_le_size t
        have ha : a.depth ≤ a.size := depth_le_size a
        have hpos := size_pos a
        rw [List.map_cons, List.map_cons, List.foldr_cons, List.sum_cons] at heq
        have hl : (l.map size).sum = 0 := by omega
        have hlnil : l = [] := eq_nil_of_sum_size_eq_zero hl
        subst hlnil
        have hda : a.depth = a.size := by
          simp only [List.map_nil, List.foldr_nil, List.sum_nil] at heq
          omega
        obtain ⟨n, rfl⟩ := ih a List.mem_cons_self hda
        exact ⟨n + 1, by rw [lineTree]⟩
  · rintro ⟨n, rfl⟩
    rw [size_lineTree, depth_lineTree]

/-! ### Trees of depth two -/

/-- The depth of a subtree is at most the maximal depth of a forest containing it. -/
lemma depth_le_foldr_max : ∀ {f : List OrdTree} {u : OrdTree}, u ∈ f →
    u.depth ≤ (f.map depth).foldr max 0
  | [], _, hu => absurd hu List.not_mem_nil
  | a :: l, u, hu => by
    rw [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.1 hu with rfl | hu'
    · exact le_max_left _ _
    · exact le_trans (depth_le_foldr_max hu') (le_max_right _ _)

/-- **The trees of depth two are the brooms**: a root with a nonempty list of leaves as
subtrees (Coq `depth_tree_eq2P`). -/
theorem depth_eq_two_iff {t : OrdTree} :
    t.depth = 2 ↔ ∃ n, t = node (List.replicate (n + 1) (node [])) := by
  constructor
  · intro h
    cases t with
    | node f =>
      rw [depth_node] at h
      have hmax : (f.map depth).foldr max 0 = 1 := by omega
      have hf : f ≠ [] := by
        rintro rfl
        simp at hmax
      have hall : ∀ u ∈ f, u = node [] := by
        intro u hu
        have hle : u.depth ≤ (f.map depth).foldr max 0 := depth_le_foldr_max hu
        have := depth_pos u
        exact depth_eq_one_iff.1 (by omega)
      refine ⟨f.length - 1, ?_⟩
      have hlen : f.length - 1 + 1 = f.length := by
        cases f with
        | nil => exact absurd rfl hf
        | cons a l => simp
      rw [hlen]
      exact congrArg node (List.eq_replicate_iff.2 ⟨rfl, hall⟩)
  · rintro ⟨n, rfl⟩
    rw [depth_node]
    have : ((List.replicate (n + 1) (node [])).map depth).foldr max 0 = 1 := by
      induction n with
      | zero => rw [List.replicate_one]; simp [depth_node]
      | succ n ih =>
        rw [List.replicate_succ, List.map_cons, List.foldr_cons, ih]
        simp [depth_node]
    rw [this]

end OrdTree
