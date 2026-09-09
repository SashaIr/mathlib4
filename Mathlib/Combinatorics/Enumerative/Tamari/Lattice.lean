/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Enumerative.Tamari.Order
public import Mathlib.Order.Finite.Lattice

/-!
# The Tamari lattice

Following `theories/Combi/bintree.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we prove that the binary trees with a
fixed number of nodes, ordered by the Tamari order, form a lattice.

The meet is read on the Tamari vectors, which by
`Tree.tamariLE_iff_forall₂_le` carry the Tamari order as the componentwise order: the
componentwise minimum of two Tamari vectors is again a Tamari vector, so it is the vector
of the meet of the two trees.  There are finitely many trees with `n` nodes and the right
comb is the greatest one, so the join then exists for general reasons
(`Finite.toLattice`).

## Main definitions and results

* `List.isTamariVector_zipWith_min` : the componentwise minimum of two Tamari vectors of
  the same length is a Tamari vector.
* `Tree.TamariOfCard n` : the binary trees with `n` nodes, ordered by the Tamari order.
* `Tree.TamariOfCard.instSemilatticeInf` : two trees with `n` nodes have a greatest lower
  bound, the tree of the componentwise minimum of their vectors.
* `Tree.TamariOfCard.instOrderTop`, `Tree.TamariOfCard.instOrderBot` : the right comb is
  the greatest element and the left comb the smallest one.
* `Tree.TamariOfCard.instLattice` : **the Tamari lattice**.
-/

@[expose] public section

namespace List

/-! ### The componentwise minimum of two Tamari vectors -/

lemma length_zipWith_min (v w : List ℕ) (h : v.length = w.length) :
    (List.zipWith min v w).length = v.length := by
  simp [h]

lemma getD_zipWith_min {v w : List ℕ} (h : v.length = w.length) (i : ℕ) :
    (List.zipWith min v w).getD i 0 = min (v.getD i 0) (w.getD i 0) := by
  by_cases hi : i < v.length
  · rw [List.getD_eq_getElem _ _ (by simpa [h] using hi), List.getElem_zipWith,
      List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (h ▸ hi)]
  · rw [List.getD_eq_default _ _ (by simp [h]; omega),
      List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    simp

/-- **The componentwise minimum of two Tamari vectors of the same length is a Tamari
vector.** -/
theorem isTamariVector_zipWith_min {v w : List ℕ} (hv : IsTamariVector v)
    (hw : IsTamariVector w) (h : v.length = w.length) :
    IsTamariVector (List.zipWith min v w) := by
  obtain ⟨hv1, hv2⟩ := isTamariVector_iff.1 hv
  obtain ⟨hw1, hw2⟩ := isTamariVector_iff.1 hw
  rw [isTamariVector_iff]
  refine ⟨fun i hi => ?_, fun i j hij hj => ?_⟩
  · rw [length_zipWith_min _ _ h] at hi ⊢
    rw [getD_zipWith_min h]
    have := hv1 i hi
    omega
  · rw [getD_zipWith_min h] at hj ⊢
    rw [getD_zipWith_min h]
    rcases le_total (v.getD i 0) (w.getD i 0) with hle | hle
    · have hmin : min (v.getD i 0) (w.getD i 0) = v.getD i 0 := min_eq_left hle
      rw [hmin] at hj ⊢
      have := hv2 i j hij hj
      omega
    · have hmin : min (v.getD i 0) (w.getD i 0) = w.getD i 0 := min_eq_right hle
      rw [hmin] at hj ⊢
      have := hw2 i j hij hj
      omega

end List

namespace BinaryTree

open List

/-! ### Finiteness -/

/-- There are finitely many Tamari vectors of a given length. -/
instance finite_tamariVector (n : ℕ) :
    Finite {v : List ℕ // IsTamariVector v ∧ v.length = n} := by
  refine Finite.of_injective (β := Fin n → Fin (n + 1))
    (fun v i => ⟨v.1.getD i 0, ?_⟩) ?_
  · have := (isTamariVector_iff.1 v.2.1).1 i (by rw [v.2.2]; exact i.2)
    rw [v.2.2] at this
    omega
  · intro v w hvw
    refine Subtype.ext (eq_of_length_eq_of_getD_eq (by rw [v.2.2, w.2.2]) fun i => ?_)
    by_cases hi : i < n
    · exact congrArg Fin.val (congrFun hvw ⟨i, hi⟩)
    · rw [List.getD_eq_default _ _ (by rw [v.2.2]; omega),
        List.getD_eq_default _ _ (by rw [w.2.2]; omega)]

instance finite_treeOfCard (n : ℕ) : Finite {t : BinaryTree Unit // t.numNodes = n} :=
  Finite.of_equiv _ (equivTamariVectorOfCard n).symm

/-! ### The meet of two trees -/

/-- The tree whose vector is the componentwise minimum of the vectors of `t` and `u`; it is
the meet of `t` and `u` for the Tamari order when they have the same number of nodes. -/
def tamariInf (t u : BinaryTree Unit) : BinaryTree Unit :=
  fromVct (List.zipWith min (rightSizes t) (rightSizes u))

lemma rightSizes_tamariInf {t u : BinaryTree Unit} (h : t.numNodes = u.numNodes) :
    rightSizes (tamariInf t u) = List.zipWith min (rightSizes t) (rightSizes u) :=
  rightSizes_fromVct (isTamariVector_zipWith_min (isTamariVector_rightSizes t)
    (isTamariVector_rightSizes u) (by simp [h]))

@[simp] lemma numNodes_tamariInf {t u : BinaryTree Unit} (h : t.numNodes = u.numNodes) :
    (tamariInf t u).numNodes = t.numNodes := by
  rw [← length_rightSizes, rightSizes_tamariInf h, length_zipWith_min _ _ (by simp [h]),
    length_rightSizes]

lemma tamariInf_le_left {t u : BinaryTree Unit} (h : t.numNodes = u.numNodes) :
    TamariLE (tamariInf t u) t := by
  refine tamariLE_of_forall₂_le (forall₂_le_iff_getD.2 ⟨?_, fun i => ?_⟩)
  · rw [rightSizes_tamariInf h, length_zipWith_min _ _ (by simp [h])]
  · rw [rightSizes_tamariInf h, getD_zipWith_min (by simp [h])]
    exact min_le_left _ _

lemma tamariInf_le_right {t u : BinaryTree Unit} (h : t.numNodes = u.numNodes) :
    TamariLE (tamariInf t u) u := by
  refine tamariLE_of_forall₂_le (forall₂_le_iff_getD.2 ⟨?_, fun i => ?_⟩)
  · rw [rightSizes_tamariInf h, length_zipWith_min _ _ (by simp [h])]
    simpa using h
  · rw [rightSizes_tamariInf h, getD_zipWith_min (by simp [h])]
    exact min_le_right _ _

lemma le_tamariInf {t u s : BinaryTree Unit} (h : t.numNodes = u.numNodes) (hst : TamariLE s t)
    (hsu : TamariLE s u) : TamariLE s (tamariInf t u) := by
  obtain ⟨hlen, hle⟩ := forall₂_le_iff_getD.1 (forall₂_le_rightSizes_of_tamariLE hst)
  obtain ⟨-, hle'⟩ := forall₂_le_iff_getD.1 (forall₂_le_rightSizes_of_tamariLE hsu)
  refine tamariLE_of_forall₂_le (forall₂_le_iff_getD.2 ⟨?_, fun i => ?_⟩)
  · rw [rightSizes_tamariInf h, length_zipWith_min _ _ (by simp [h])]
    exact hlen
  · rw [rightSizes_tamariInf h, getD_zipWith_min (by simp [h])]
    exact le_min (hle i) (hle' i)

/-! ### The Tamari lattice -/

/-- The binary trees with `n` nodes, ordered by the Tamari order. -/
def TamariOfCard (n : ℕ) : Type := {t : BinaryTree Unit // t.numNodes = n}

namespace TamariOfCard

variable {n : ℕ}

instance : CoeOut (TamariOfCard n) (BinaryTree Unit) := ⟨Subtype.val⟩

instance : Finite (TamariOfCard n) := finite_treeOfCard n

instance instPartialOrder : PartialOrder (TamariOfCard n) where
  le t u := TamariLE t.1 u.1
  le_refl t := tamariLE_refl t.1
  le_trans _ _ _ h1 h2 := tamariLE_trans h1 h2
  le_antisymm _ _ h1 h2 := Subtype.ext (tamariLE_antisymm h1 h2)

lemma le_def {t u : TamariOfCard n} : t ≤ u ↔ TamariLE t.1 u.1 := Iff.rfl

instance instSemilatticeInf : SemilatticeInf (TamariOfCard n) where
  inf t u := ⟨tamariInf t.1 u.1, by rw [numNodes_tamariInf (t.2.trans u.2.symm), t.2]⟩
  inf_le_left t u := tamariInf_le_left (t.2.trans u.2.symm)
  inf_le_right t u := tamariInf_le_right (t.2.trans u.2.symm)
  le_inf _ t u h1 h2 := le_tamariInf (t.2.trans u.2.symm) h1 h2

instance instOrderTop : OrderTop (TamariOfCard n) where
  top := ⟨combRight n, numNodes_combRight n⟩
  le_top t := by
    have := tamariLE_combRight t.1
    rw [t.2] at this
    exact this

instance instOrderBot : OrderBot (TamariOfCard n) where
  bot := ⟨combLeft n, numNodes_combLeft n⟩
  bot_le t := by
    have := combLeft_tamariLE t.1
    rw [t.2] at this
    exact this

@[simp] lemma inf_val (t u : TamariOfCard n) : (t ⊓ u).1 = tamariInf t.1 u.1 := rfl

@[simp] lemma top_val : (⊤ : TamariOfCard n).1 = combRight n := rfl

@[simp] lemma bot_val : (⊥ : TamariOfCard n).1 = combLeft n := rfl

/-- **The Tamari lattice**: the binary trees with `n` nodes form a lattice for the Tamari
order.  The meet is the tree of the componentwise minimum of the two Tamari vectors, and
the join exists because there are finitely many trees with `n` nodes and the right comb is
the greatest one. -/
noncomputable instance instLattice : Lattice (TamariOfCard n) := Finite.toLattice _

end TamariOfCard

end BinaryTree
