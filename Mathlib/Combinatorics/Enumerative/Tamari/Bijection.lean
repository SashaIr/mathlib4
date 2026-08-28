/-
Copyright (c) 2026 Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Enumerative.Tamari.Vector

/-!
# Binary trees are in bijection with Tamari vectors

Following `theories/Combi/bintree.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we build the inverse `Tree.fromVct` of
the map `List.rightSizes` sending a binary tree to the vector of the sizes of the right
subtrees of its nodes, and we prove that it is indeed a two-sided inverse on the Tamari
vectors.  This gives the bijection between binary trees with `n` nodes and Tamari vectors
of length `n`.

The tree `Tree.fromVct v` is built from left to right: the head `v₀` of `v` says that the
next node carries, as its right subtree, the tree built from the `v₀` following entries;
the remaining entries are then grafted, one after the other, along the left spine, which
is what the auxiliary operation `Tree.catLeft` does.

## Main definitions and results

* `Tree.catLeft a b` : the tree `b` grafted at the bottom of the left spine of `a` (Coq
  `cat_left`).
* `Tree.fromVct v` : the binary tree associated to a Tamari vector (Coq `from_vct`).
* `Tree.fromVct_rightSizes` : `Tree.fromVct` is a left inverse of `List.rightSizes` (Coq
  `right_sizesK`).
* `List.rightSizes_fromVct` : `Tree.fromVct` is a right inverse of `List.rightSizes` on
  the Tamari vectors (Coq `from_vctK`).
* `Tree.equivTamariVector` and `Tree.equivTamariVectorOfCard` : the resulting bijections
  between binary trees and Tamari vectors, and between the trees with `n` nodes and the
  Tamari vectors of length `n` (Coq `bintreeoftype_TamariVector_bij`).
-/

namespace List

/-- A suffix of a Tamari vector is a Tamari vector. -/
lemma IsTamariVector.drop {v : List ℕ} (h : IsTamariVector v) (k : ℕ) :
    IsTamariVector (v.drop k) := by
  induction k generalizing v with
  | zero => simpa using h
  | succ k ih =>
    match v with
    | [] => simp
    | v0 :: v =>
      rw [List.drop_succ_cons]
      exact ih (isTamariVector_cons_iff.1 h).2.1

/-- If `v₀ :: v` is a Tamari vector then so is the prefix of `v` of length `v₀`, which is
the vector encoding the right subtree of the first node. -/
lemma IsTamariVector.take_of_cons {v0 : ℕ} {v : List ℕ} (h : IsTamariVector (v0 :: v)) :
    IsTamariVector (v.take v0) := by
  obtain ⟨hlen, htail, hlt⟩ := isTamariVector_cons_iff.1 h
  obtain ⟨-, h2⟩ := isTamariVector_iff.1 htail
  have hlent : (v.take v0).length = v0 := by simp [hlen]
  have hget : ∀ i < v0, (v.take v0).getD i 0 = v.getD i 0 := fun i hi => by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, hi, if_true]
  rw [isTamariVector_iff]
  refine ⟨fun i hi => ?_, fun i j hij hj => ?_⟩
  · rw [hlent] at hi ⊢
    rw [hget i hi]
    exact hlt i hi
  · by_cases hi : i < v0
    · rw [hget i hi] at hj ⊢
      have hjv : j < v0 := lt_of_le_of_lt hj (hlt i hi)
      rw [hget j hjv]
      exact h2 i j hij hj
    · rw [List.getD_eq_default _ 0 (by omega)] at hj ⊢
      omega

end List

namespace Tree

/-! ### Grafting along the left spine -/

/-- The tree obtained by grafting `a` at the bottom of the left spine of `b` (Coq
`cat_left`). -/
def catLeft : Tree Unit → Tree Unit → Tree Unit
  | a, .nil => a
  | a, .node _ l r => .node () (catLeft a l) r

@[simp] lemma catLeft_nil (a : Tree Unit) : catLeft a .nil = a := rfl

@[simp] lemma catLeft_node (a l r : Tree Unit) :
    catLeft a (Tree.node () l r) = Tree.node () (catLeft a l) r := rfl

@[simp] lemma nil_catLeft (t : Tree Unit) : catLeft .nil t = t := by
  induction t with
  | nil => rfl
  | node a l r ihl _ => cases a; rw [catLeft_node, ihl]

lemma catLeft_assoc (a b c : Tree Unit) :
    catLeft (catLeft a b) c = catLeft a (catLeft b c) := by
  induction c with
  | nil => rfl
  | node x l r ihl _ => cases x; simp [ihl]

/-- Grafting concatenates the vectors of the sizes of the right subtrees. -/
@[simp] lemma rightSizes_catLeft (a b : Tree Unit) :
    List.rightSizes (catLeft a b) = List.rightSizes a ++ List.rightSizes b := by
  induction b with
  | nil => simp
  | node x l r ihl _ => cases x; simp [ihl]

/-! ### The tree associated to a Tamari vector -/

/-- Auxiliary function for `Tree.fromVct`: `Tree.fromVctAux lft v` grafts the tree built
from `v` at the bottom of the left spine of `lft` (Coq `from_vct_rec`). -/
def fromVctAux : Tree Unit → List ℕ → Tree Unit
  | lft, [] => lft
  | lft, v0 :: v => fromVctAux (Tree.node () lft (fromVctAux .nil (v.take v0))) (v.drop v0)
termination_by _ v => v.length

/-- The binary tree associated to a Tamari vector (Coq `from_vct`). -/
def fromVct (v : List ℕ) : Tree Unit := fromVctAux .nil v

lemma fromVctAux_nil (lft : Tree Unit) : fromVctAux lft [] = lft := by rw [fromVctAux]

lemma fromVctAux_cons (lft : Tree Unit) (v0 : ℕ) (v : List ℕ) :
    fromVctAux lft (v0 :: v)
      = fromVctAux (Tree.node () lft (fromVctAux .nil (v.take v0))) (v.drop v0) := by
  rw [fromVctAux]

@[simp] lemma fromVct_nil : fromVct [] = .nil := fromVctAux_nil _

lemma fromVct_cons (v0 : ℕ) (v : List ℕ) :
    fromVct (v0 :: v)
      = fromVctAux (Tree.node () .nil (fromVct (v.take v0))) (v.drop v0) :=
  fromVctAux_cons _ _ _

/-- The auxiliary function only grafts the tree built from its second argument. -/
theorem fromVctAux_eq_catLeft (lft : Tree Unit) (v : List ℕ) :
    fromVctAux lft v = catLeft lft (fromVct v) := by
  match v with
  | [] => rw [fromVctAux_nil, fromVct_nil, catLeft_nil]
  | v0 :: v =>
    rw [fromVctAux_cons, fromVct, fromVctAux_cons,
      fromVctAux_eq_catLeft (Tree.node () lft _),
      fromVctAux_eq_catLeft (Tree.node () .nil _), ← catLeft_assoc]
    simp
termination_by v.length

/-! ### The two-sided inverse -/

theorem fromVctAux_rightSizes_append (t : Tree Unit) (lft : Tree Unit) (w : List ℕ) :
    fromVctAux lft (List.rightSizes t ++ w) = fromVctAux (catLeft lft t) w := by
  match t with
  | .nil => simp [List.rightSizes]
  | .node x l r =>
    cases x
    rw [List.rightSizes_node, List.append_assoc, fromVctAux_rightSizes_append l,
      List.cons_append, fromVctAux_cons]
    have hlen : (List.rightSizes r).length = r.numNodes := by simp
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
      List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega),
      List.nil_append]
    have hr : fromVctAux .nil (List.rightSizes r) = r := by
      have := fromVctAux_rightSizes_append r .nil []
      rwa [List.append_nil, fromVctAux_nil, nil_catLeft] at this
    rw [hr, catLeft_node]
termination_by t.numNodes

/-- **`Tree.fromVct` is a left inverse of `List.rightSizes`** (Coq `right_sizesK`). -/
theorem fromVct_rightSizes (t : Tree Unit) : fromVct (List.rightSizes t) = t := by
  have := fromVctAux_rightSizes_append t .nil []
  rwa [List.append_nil, fromVctAux_nil, nil_catLeft, ← fromVct] at this

/-- **`Tree.fromVct` is a right inverse of `List.rightSizes` on the Tamari vectors** (Coq
`from_vctK`). -/
theorem _root_.List.rightSizes_fromVct {v : List ℕ} (hv : List.IsTamariVector v) :
    List.rightSizes (fromVct v) = v := by
  match v with
  | [] => simp
  | v0 :: v =>
    obtain ⟨hlen, htail, -⟩ := List.isTamariVector_cons_iff.1 hv
    have htake : List.rightSizes (fromVct (v.take v0)) = v.take v0 :=
      List.rightSizes_fromVct hv.take_of_cons
    have hdrop : List.rightSizes (fromVct (v.drop v0)) = v.drop v0 :=
      List.rightSizes_fromVct (htail.drop v0)
    have hnum : (fromVct (v.take v0)).numNodes = v0 := by
      rw [← List.length_rightSizes, htake]
      simp [hlen]
    rw [fromVct_cons, fromVctAux_eq_catLeft, rightSizes_catLeft, List.rightSizes_node,
      htake, hdrop, hnum]
    simp
termination_by v.length
decreasing_by
  · exact lt_of_le_of_lt (by simp) (Nat.lt_succ_self _)
  · exact lt_of_le_of_lt (by simp) (Nat.lt_succ_self _)

/-! ### The bijection -/

/-- **Binary trees are in bijection with Tamari vectors** (Coq
`bintreeoftype_TamariVector_bij`). -/
@[simps] def equivTamariVector : Tree Unit ≃ {v : List ℕ // List.IsTamariVector v} where
  toFun t := ⟨List.rightSizes t, List.isTamariVector_rightSizes t⟩
  invFun v := fromVct v.1
  left_inv t := fromVct_rightSizes t
  right_inv v := Subtype.ext (List.rightSizes_fromVct v.2)

/-- **Binary trees with `n` nodes are in bijection with Tamari vectors of length `n`**
(Coq `bintreeoftype_TamariVector_bij`). -/
def equivTamariVectorOfCard (n : ℕ) :
    {t : Tree Unit // t.numNodes = n} ≃ {v : List ℕ // List.IsTamariVector v ∧ v.length = n} :=
  (equivTamariVector.subtypeEquiv (fun t => by
    simp only [equivTamariVector_apply_coe, List.length_rightSizes])).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter _ _)

end Tree
