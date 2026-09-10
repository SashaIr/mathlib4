/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Enumerative.Tamari.Bijection

/-!
# The Tamari order read on Tamari vectors

Following `theories/Combi/bintree.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we describe the rotations of a binary
tree on the vector `List.rightSizes t` of the sizes of the right subtrees of its nodes, and
we deduce that the Tamari order `Tree.TamariLE` is the componentwise order on Tamari
vectors.

A rotation changes exactly one entry of the vector: rotating `((a, b), r)` into
`(a, (b, r))` replaces the entry `|b|` of the node carrying `b`, sitting at the index
`i = |a|`, by `|b| + 1 + |r|`, all the other entries being unchanged.  The index `i` is
the index of a rotation exactly when the node `i` is the left child of its parent, which
happens exactly when the node `j = i + vᵢ + 1` following the block `[i, i + vᵢ]` of `i`
exists and no earlier block ends where the block of `i` does (`List.IsRotIdx`).

## Main definitions and results

* `List.vctRotate v i` : the vector obtained from `v` by the rotation at the index `i`.
* `List.IsRotIdx v i` : `i` is the index of a rotation of `v`.
* `Tree.exists_mem_rotations_rightSizes_eq` : every rotation of the vector of a tree is
  realised by a rotation of the tree.
* `Tree.tamariLE_iff_forall₂_le` : **the Tamari order is the componentwise order on the
  Tamari vectors**.
-/

@[expose] public section

namespace List

variable {v w : List ℕ}

/-- Two lists of naturals are componentwise comparable exactly when they have the same
length and all their entries, read with `getD`, are comparable. -/
lemma forall₂_le_iff_getD :
    Forall₂ (· ≤ ·) v w ↔ v.length = w.length ∧ ∀ i, v.getD i 0 ≤ w.getD i 0 := by
  rw [List.forall₂_iff_get]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun i => ?_⟩
    by_cases hi : i < v.length
    · rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (h1 ▸ hi)]
      exact h2 i hi (h1 ▸ hi)
    · rw [List.getD_eq_default _ _ (by omega)]
      exact Nat.zero_le _
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun i hi hi' => ?_⟩
    have := h2 i
    rwa [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi'] at this

/-! ### Rotations of a vector -/

/-- The vector obtained from `v` by the rotation at the index `i`: the entry `vᵢ` is
replaced by `vᵢ + 1 + v_j`, where `j = i + vᵢ + 1` is the index following the block of
`i`. -/
def vctRotate (v : List ℕ) (i : ℕ) : List ℕ :=
  v.set i (v.getD i 0 + 1 + v.getD (i + v.getD i 0 + 1) 0)

/-- `i` is the index of a rotation of the vector `v`: the index `j = i + vᵢ + 1` following
the block of `i` exists, and no earlier block ends where the block of `i` does.  For the
vector of a tree, this says that the node `i` is the left child of its parent. -/
structure IsRotIdx (v : List ℕ) (i : ℕ) : Prop where
  /-- The block of `i` is followed by a further entry. -/
  lt : i + v.getD i 0 + 1 < v.length
  /-- No block starting earlier ends where the block of `i` does. -/
  ne : ∀ p < i, p + v.getD p 0 ≠ i + v.getD i 0

@[simp] lemma length_vctRotate (v : List ℕ) (i : ℕ) : (vctRotate v i).length = v.length := by
  simp [vctRotate]

lemma getD_vctRotate_of_ne {i k : ℕ} (h : k ≠ i) :
    (vctRotate v i).getD k 0 = v.getD k 0 := by
  by_cases hk : k < v.length
  · rw [vctRotate, List.getD_eq_getElem _ _ (by simpa using hk),
      List.getD_eq_getElem _ _ hk, List.getElem_set_ne (Ne.symm h)]
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hk),
      List.getD_eq_default _ _ (Nat.le_of_not_lt hk)]

lemma getD_vctRotate_self {i : ℕ} (h : i < v.length) :
    (vctRotate v i).getD i 0 = v.getD i 0 + 1 + v.getD (i + v.getD i 0 + 1) 0 := by
  rw [vctRotate, List.getD_eq_getElem _ _ (by simpa using h), List.getElem_set_self]

lemma lt_getD_vctRotate_self {i : ℕ} (h : i < v.length) :
    v.getD i 0 < (vctRotate v i).getD i 0 := by
  rw [getD_vctRotate_self h]
  omega

lemma forall₂_le_vctRotate {i : ℕ} : Forall₂ (· ≤ ·) v (vctRotate v i) := by
  refine forall₂_le_iff_getD.2 ⟨by simp, fun k => ?_⟩
  by_cases hk : k = i
  · subst hk
    by_cases h : k < v.length
    · exact (lt_getD_vctRotate_self h).le
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt h)]
      exact Nat.zero_le _
  · rw [getD_vctRotate_of_ne hk]

end List

namespace BinaryTree

open List

/-! ### A rotation increases the vector -/

/-- A rotation increases the vector of the sizes of the right subtrees, componentwise. -/
theorem forall₂_le_rightSizes_of_mem_rotations {t u : BinaryTree Unit} (h : u ∈ rotations t) :
    Forall₂ (· ≤ ·) (rightSizes t) (rightSizes u) := by
  induction t generalizing u with
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
        simp only [rightSizes_node, List.append_assoc, List.cons_append]
        refine List.rel_append (forall₂_same.2 fun _ _ => le_refl _) (List.Forall₂.cons ?_ ?_)
        · simp only [BinaryTree.numNodes]
          omega
        · exact List.rel_append (forall₂_same.2 fun _ _ => le_refl _)
            (List.Forall₂.cons (le_refl _) (forall₂_same.2 fun _ _ => le_refl _))
    · obtain ⟨lr, hlr, rfl⟩ := h
      exact List.rel_append (ihl hlr)
        (List.Forall₂.cons (le_refl _) (forall₂_same.2 fun _ _ => le_refl _))
    · obtain ⟨rr, hrr, rfl⟩ := h
      exact List.rel_append (forall₂_same.2 fun _ _ => le_refl _)
        (List.Forall₂.cons (numNodes_of_mem_rotations hrr).ge (ihr hrr))

/-- Comparable trees for the Tamari order have componentwise comparable vectors. -/
theorem forall₂_le_rightSizes_of_tamariLE {t u : BinaryTree Unit} (h : TamariLE t u) :
    Forall₂ (· ≤ ·) (rightSizes t) (rightSizes u) := by
  induction h with
  | refl => exact forall₂_same.2 fun _ _ => le_refl _
  | tail _ hstep ih =>
    refine forall₂_le_iff_getD.2 ⟨?_, fun i => ?_⟩
    · rw [(forall₂_le_iff_getD.1 ih).1,
        (forall₂_le_iff_getD.1 (forall₂_le_rightSizes_of_mem_rotations hstep)).1]
    · exact le_trans ((forall₂_le_iff_getD.1 ih).2 i)
        ((forall₂_le_iff_getD.1 (forall₂_le_rightSizes_of_mem_rotations hstep)).2 i)

end BinaryTree

/-! ### Every rotation of the vector comes from a rotation of the tree -/

namespace BinaryTree

open List

/-- The block `[i, i + vᵢ]` of a node of a tree stays inside the tree. -/
lemma add_getD_rightSizes_lt {t : BinaryTree Unit} {i : ℕ} (h : i < t.numNodes) :
    i + (rightSizes t).getD i 0 < t.numNodes := by
  have := (isTamariVector_iff.1 (isTamariVector_rightSizes t)).1 i (by simpa using h)
  rw [length_rightSizes] at this
  omega

/-- The rotation at the root: if the block of `i` fills the left subtree `l` of the root,
then `i` is the root of `l` and the rotation at `i` is the rotation at the root. -/
lemma exists_mem_rotations_root {l r : BinaryTree Unit} {i : ℕ}
    (heq : i + (rightSizes l).getD i 0 + 1 = l.numNodes)
    (hne : ∀ p < i, p + (rightSizes l).getD p 0 ≠ i + (rightSizes l).getD i 0) :
    ∃ u ∈ rotations (node () l r), rightSizes u = vctRotate (rightSizes (node () l r)) i := by
  match l with
  | .nil => simp only [BinaryTree.numNodes] at heq; omega
  | .node b x y =>
    cases b
    have hlenx : (rightSizes x).length = x.numNodes := length_rightSizes x
    have hleny : (rightSizes y).length = y.numNodes := length_rightSizes y
    have hgetX : ∀ (z : List ℕ) (c : ℕ), (rightSizes x ++ c :: z).getD x.numNodes 0 = c := by
      intro z c
      rw [← hlenx]
      exact getD_append_cons_self
    have hnn : ∀ z w : BinaryTree Unit, (BinaryTree.node () z w).numNodes =
        z.numNodes + w.numNodes + 1 := by
      intro z w
      simp only [BinaryTree.numNodes]
    rw [rightSizes_node] at heq hne
    rw [hnn] at heq
    -- the index `i` is the root of `l`, that is `i = |x|`
    have hix : i = x.numNodes := by
      rcases lt_trichotomy i x.numNodes with hi | hi | hi
      · have hb := add_getD_rightSizes_lt (t := x) (i := i) hi
        rw [getD_append_cons_left (by omega)] at heq
        omega
      · exact hi
      · exact absurd (by rw [hgetX]; omega) (hne x.numNodes hi)
    subst hix
    refine ⟨BinaryTree.node () x (BinaryTree.node () y r), by rw [rotations_node]; simp, ?_⟩
    have h1 : rightSizes (BinaryTree.node () x (BinaryTree.node () y r))
        = rightSizes x ++ (y.numNodes + r.numNodes + 1) ::
            (rightSizes y ++ r.numNodes :: rightSizes r) := by
      rw [rightSizes_node, rightSizes_node, hnn]
    have h2 : rightSizes (BinaryTree.node () (BinaryTree.node () x y) r)
        = rightSizes x ++ y.numNodes :: (rightSizes y ++ r.numNodes :: rightSizes r) := by
      simp only [rightSizes_node, List.append_assoc, List.cons_append]
    have h3 : (rightSizes x ++ y.numNodes :: (rightSizes y ++ r.numNodes :: rightSizes r)).getD
        (x.numNodes + y.numNodes + 1) 0 = r.numNodes := by
      rw [← hlenx, show (rightSizes x).length + y.numNodes + 1
            = (rightSizes x).length + 1 + y.numNodes by omega,
        getD_append_cons_right, ← hleny, getD_append_cons_self]
    rw [h1, vctRotate, h2, hgetX, h3, ← hlenx, set_append_cons_self]
    congr 2
    omega

/-- **Every rotation of the vector of a tree is realised by a rotation of the tree**: if
`i` is the index of a rotation of `List.rightSizes t`, there is a rotation `u` of `t` whose
vector is the rotated vector. -/
theorem exists_mem_rotations_rightSizes_eq :
  ∀ {t : BinaryTree Unit} {i : ℕ}, IsRotIdx (rightSizes t) i →
      ∃ u ∈ rotations t, rightSizes u = vctRotate (rightSizes t) i := by
  intro t
  induction t with
  | nil =>
    intro i h
    exact absurd h.lt (by simp)
  | node a l r ihl ihr =>
    cases a
    intro i h
    have hlenl : (rightSizes l).length = l.numNodes := length_rightSizes l
    have hlenr : (rightSizes r).length = r.numNodes := length_rightSizes r
    have hv : rightSizes (BinaryTree.node () l r) =
        rightSizes l ++ r.numNodes :: rightSizes r := rfl
    rw [hv] at h ⊢
    have hlenv : (rightSizes l ++ r.numNodes :: rightSizes r).length
        = l.numNodes + 1 + r.numNodes := by
      simp only [List.length_append, List.length_cons, hlenl, hlenr]
      omega
    rcases lt_trichotomy i l.numNodes with hi | hi | hi
    · -- the rotation happens inside the left subtree
      have hgi : (rightSizes l ++ r.numNodes :: rightSizes r).getD i 0 = (rightSizes l).getD i 0 :=
        getD_append_cons_left (by omega)
      have hne_l : ∀ p < i, p + (rightSizes l).getD p 0 ≠ i + (rightSizes l).getD i 0 := by
        intro p hp
        have hp' := h.ne p hp
        rwa [hgi, getD_append_cons_left (by omega : p < (rightSizes l).length)] at hp'
      have hblock : i + (rightSizes l).getD i 0 < l.numNodes := add_getD_rightSizes_lt hi
      rcases lt_or_eq_of_le (Nat.succ_le_of_lt hblock) with hlt | heq
      · obtain ⟨ul, hul, hres⟩ := ihl ⟨by omega, hne_l⟩
        refine ⟨BinaryTree.node () ul r, by rw [rotations_node]; simp [hul], ?_⟩
        rw [rightSizes_node, hres, vctRotate, vctRotate, hgi,
          getD_append_cons_left
            (by omega : i + (rightSizes l).getD i 0 + 1 < (rightSizes l).length),
          set_append_cons_left (by omega)]
      · rw [← hv]
        exact exists_mem_rotations_root (by omega) hne_l
    · -- the root of the tree is never the index of a rotation
      exfalso
      have hgi : (rightSizes l ++ r.numNodes :: rightSizes r).getD i 0 = r.numNodes := by
        rw [hi, ← hlenl]
        exact getD_append_cons_self
      have hlt := h.lt
      rw [hgi, hlenv] at hlt
      omega
    · -- the rotation happens inside the right subtree
      obtain ⟨k, rfl⟩ : ∃ k, i = l.numNodes + 1 + k := ⟨i - l.numNodes - 1, by omega⟩
      have hgi : ∀ p, (rightSizes l ++ r.numNodes :: rightSizes r).getD (l.numNodes + 1 + p) 0
          = (rightSizes r).getD p 0 := by
        intro p
        rw [← hlenl]
        exact getD_append_cons_right
      have hlt := h.lt
      rw [hgi, hlenv] at hlt
      have hne_r : ∀ p < k, p + (rightSizes r).getD p 0 ≠ k + (rightSizes r).getD k 0 := by
        intro p hp
        have hp' := h.ne (l.numNodes + 1 + p) (by omega)
        rw [hgi, hgi] at hp'
        omega
      obtain ⟨ur, hur, hres⟩ := ihr ⟨by omega, hne_r⟩
      refine ⟨BinaryTree.node () l ur, by rw [rotations_node]; simp [hur], ?_⟩
      rw [rightSizes_node, hres, numNodes_of_mem_rotations hur, vctRotate, vctRotate, hgi,
        show l.numNodes + 1 + k + (rightSizes r).getD k 0 + 1
          = l.numNodes + 1 + (k + (rightSizes r).getD k 0 + 1) by omega, hgi, ← hlenl,
        set_append_cons_right]

end BinaryTree

/-! ### The Tamari order is the componentwise order -/

namespace List

/-- A componentwise inequality between two lists with the same sum is an equality. -/
lemma eq_of_forall₂_le_of_sum_eq {v w : List ℕ} (h : Forall₂ (· ≤ ·) v w)
    (hs : v.sum = w.sum) : v = w := by
  induction h with
  | nil => rfl
  | @cons a b l m hab _ ih =>
    have hl : l.sum ≤ m.sum := List.Forall₂.sum_le_sum ‹Forall₂ (· ≤ ·) l m›
    simp only [List.sum_cons] at hs
    rw [ih (by omega), show a = b by omega]

end List

namespace BinaryTree

open List

/-- If the vector of `t` is componentwise smaller than that of `u` and they are not equal,
the least index where they differ is the index of a rotation of the vector of `t`. -/
lemma isRotIdx_find {t u : BinaryTree Unit} (h : Forall₂ (· ≤ ·) (rightSizes t) (rightSizes u))
    {i : ℕ} (hlt : (rightSizes t).getD i 0 < (rightSizes u).getD i 0)
    (hmin : ∀ p < i, (rightSizes t).getD p 0 = (rightSizes u).getD p 0) :
    IsRotIdx (rightSizes t) i := by
  obtain ⟨hlen, hle⟩ := forall₂_le_iff_getD.1 h
  obtain ⟨hw1, hw2⟩ := isTamariVector_iff.1 (isTamariVector_rightSizes u)
  have hi : i < (rightSizes u).length := by
    by_contra hi
    rw [List.getD_eq_default (rightSizes u) 0 (by omega)] at hlt
    omega
  have hiu := hw1 i hi
  refine ⟨by omega, fun p hp hpe => ?_⟩
  have hpu : (rightSizes t).getD p 0 = (rightSizes u).getD p 0 := hmin p hp
  have := hw2 p i hp (by omega)
  omega

/-- **The componentwise order on the vectors implies the Tamari order.** -/
theorem tamariLE_of_forall₂_le_aux :
    ∀ (d : ℕ) {t u : BinaryTree Unit}, (rightSizes u).sum - (rightSizes t).sum ≤ d →
      Forall₂ (· ≤ ·) (rightSizes t) (rightSizes u) → TamariLE t u := by
  intro d
  induction d with
  | zero =>
    intro t u hd h
    have hs : (rightSizes t).sum ≤ (rightSizes u).sum := List.Forall₂.sum_le_sum h
    have : rightSizes t = rightSizes u := eq_of_forall₂_le_of_sum_eq h (by omega)
    have ht : t = u := by
      rw [← fromVct_rightSizes t, ← fromVct_rightSizes u, this]
    exact ht ▸ tamariLE_refl t
  | succ d ih =>
    intro t u hd h
    obtain ⟨hlen, hle⟩ := forall₂_le_iff_getD.1 h
    by_cases hEq : rightSizes t = rightSizes u
    · have ht : t = u := by
        rw [← fromVct_rightSizes t, ← fromVct_rightSizes u, hEq]
      exact ht ▸ tamariLE_refl t
    · have hex : ∃ i, (rightSizes t).getD i 0 < (rightSizes u).getD i 0 := by
        by_contra hcon
        push Not at hcon
        exact hEq (eq_of_length_eq_of_getD_eq hlen fun i => le_antisymm (hle i) (hcon i))
      classical
      set i := Nat.find hex with hi
      have hlt : (rightSizes t).getD i 0 < (rightSizes u).getD i 0 := Nat.find_spec hex
      have hmin : ∀ p < i, (rightSizes t).getD p 0 = (rightSizes u).getD p 0 := fun p hp =>
        le_antisymm (hle p) (by simpa using Nat.find_min hex hp)
      have hrot : IsRotIdx (rightSizes t) i := isRotIdx_find h hlt hmin
      obtain ⟨t', ht', hres⟩ := exists_mem_rotations_rightSizes_eq hrot
      -- the rotated vector is still below that of `u`
      have hle' : Forall₂ (· ≤ ·) (rightSizes t') (rightSizes u) := by
        obtain ⟨hw1, hw2⟩ := isTamariVector_iff.1 (isTamariVector_rightSizes u)
        have hi' : i < (rightSizes t).length := by
          by_contra hcon
          rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)] at hlt
          omega
        refine forall₂_le_iff_getD.2 ⟨by rw [hres]; simpa using hlen, fun k => ?_⟩
        by_cases hk : k = i
        · subst hk
          rw [hres, getD_vctRotate_self hi']
          have h1 := hw1 i (by omega)
          have h2 := hw2 i (i + (rightSizes t).getD i 0 + 1) (by omega) (by omega)
          have h3 := hle (i + (rightSizes t).getD i 0 + 1)
          omega
        · rw [hres, getD_vctRotate_of_ne hk]
          exact hle k
      -- and the sum has strictly increased
      have hsum : (rightSizes t).sum < (rightSizes t').sum := by
        have := rightSizesSum_lt_of_mem_rotations ht'
        rwa [← sum_rightSizes, ← sum_rightSizes] at this
      exact tamariLE_trans (tamariLE_of_mem_rotations ht') (ih (by omega) hle')

/-- **The componentwise order on the vectors implies the Tamari order.** -/
theorem tamariLE_of_forall₂_le {t u : BinaryTree Unit}
    (h : Forall₂ (· ≤ ·) (rightSizes t) (rightSizes u)) : TamariLE t u :=
  tamariLE_of_forall₂_le_aux _ le_rfl h

/-- **The Tamari order is the componentwise order on the Tamari vectors**: a binary tree is
below another one for the Tamari order exactly when the sizes of the right subtrees of its
nodes, read in infix order, are all at most those of the other one. -/
theorem tamariLE_iff_forall₂_le {t u : BinaryTree Unit} :
    TamariLE t u ↔ Forall₂ (· ≤ ·) (rightSizes t) (rightSizes u) :=
  ⟨forall₂_le_rightSizes_of_tamariLE, tamariLE_of_forall₂_le⟩

end BinaryTree
