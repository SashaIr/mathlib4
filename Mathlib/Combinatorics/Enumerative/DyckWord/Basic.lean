/-
Copyright (c) 2026 Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Data.Nat.SuccPred

/-!
# Dyck words

A Lean 4 port of `theories/Combi/Dyckword.v` from
[Coq-Combi](https://github.com/math-comp/Coq-Combi).

A *Dyck word* is a word on the two letter alphabet `(` and `)` which is well
parenthesized: every prefix contains at least as many `(` as `)`, and the total
numbers of `(` and of `)` agree.  Following Mathlib the two letters are the two
constructors `DyckStep.U` and `DyckStep.D`.

As in the Coq development, Dyck words are handled here as plain lists satisfying
a predicate (Coq's `Dyck_word`), the counting function being the *height*
`dyckHeight w`, the number of `U`s minus the number of `D`s.  The bundled
structure `DyckWord` of Mathlib plays the role of Coq's sigma type `Dyck`, and
`List.isDyckWord_iff_exists_dyckWord` is the dictionary between the two.

## Main definitions

* `List.dyckHeight w` : the height of a word (Coq `height`).
* `List.IsDyckPrefix w` : every prefix of `w` has nonnegative height (Coq
  `Dyck_prefix`).
* `List.IsDyckWord w` : `w` is a Dyck word (Coq `Dyck_word`).

## Main results

* `List.isDyckWord_append`, `List.isDyckWord_nest`, `List.isDyckWord_join`,
  `List.isDyckWord_flatten` : the stability properties of Dyck words (Coq
  `Dyck_word_cat`, `Dyck_word_OwC`, `Dyck_word_OwCw`, `Dyck_word_flatten`).
* `List.exists_join_of_isDyckWord` : the standard factorization `D = (D₁)D₂` of a
  nonempty Dyck word (Coq `factor_Dyck`), and `List.join_eq_join_iff` for its
  uniqueness (Coq `join_Dyck_inj`).
* `List.IsDyckWord.induction` : the induction principle attached to the standard
  factorization (Coq `Dyck_ind`).
* `List.even_length_of_isDyckWord` : a Dyck word has even length (Coq
  `Dyck_size_even`).
* `List.card_isDyckWord_length_eq_catalan` : there are `catalan n` Dyck words of
  length `2 * n` (Coq `card_Dyck_hsz`, proved there by the rotation argument which is
  ported in `Mathlib/Combinatorics/Enumerative/DyckWord/Rotation.lean`).
-/

namespace List

open List DyckStep

/-! ### The height of a word -/

/-- The height of a word: the number of `U`s minus the number of `D`s (Coq `height`). -/
def dyckHeight (w : List DyckStep) : ℤ := (w.count U : ℤ) - (w.count D : ℤ)

@[simp] lemma dyckHeight_nil : dyckHeight [] = 0 := by simp [dyckHeight]

lemma dyckHeight_singleton_U : dyckHeight [U] = 1 := by simp [dyckHeight]

lemma dyckHeight_singleton_D : dyckHeight [D] = -1 := by simp [dyckHeight]

@[simp] lemma dyckHeight_cons_U (w : List DyckStep) :
    dyckHeight (U :: w) = dyckHeight w + 1 := by
  have h1 : (U :: w).count U = w.count U + 1 := by simp
  have h2 : (U :: w).count D = w.count D := by simp
  simp only [dyckHeight, h1, h2]
  push_cast
  ring

@[simp] lemma dyckHeight_cons_D (w : List DyckStep) :
    dyckHeight (D :: w) = dyckHeight w - 1 := by
  have h1 : (D :: w).count U = w.count U := by simp
  have h2 : (D :: w).count D = w.count D + 1 := by simp
  simp only [dyckHeight, h1, h2]
  push_cast
  ring

lemma dyckHeight_append (u v : List DyckStep) :
    dyckHeight (u ++ v) = dyckHeight u + dyckHeight v := by
  simp only [dyckHeight, count_append]
  push_cast
  ring

@[simp] lemma dyckHeight_concat_D (w : List DyckStep) :
    dyckHeight (w ++ [D]) = dyckHeight w - 1 := by
  rw [dyckHeight_append, dyckHeight_singleton_D]
  ring

@[simp] lemma dyckHeight_concat_U (w : List DyckStep) :
    dyckHeight (w ++ [U]) = dyckHeight w + 1 := by
  rw [dyckHeight_append, dyckHeight_singleton_U]

@[simp] lemma dyckHeight_reverse (w : List DyckStep) :
    dyckHeight w.reverse = dyckHeight w := by
  simp [dyckHeight]

lemma dyckHeight_take_add_dyckHeight_drop (n : ℕ) (w : List DyckStep) :
    dyckHeight (w.take n) + dyckHeight (w.drop n) = dyckHeight w := by
  rw [← dyckHeight_append, take_append_drop]

lemma dyckHeight_drop (n : ℕ) (w : List DyckStep) :
    dyckHeight (w.drop n) = dyckHeight w - dyckHeight (w.take n) := by
  have := dyckHeight_take_add_dyckHeight_drop n w
  omega

lemma dyckHeight_replicate_U (n : ℕ) : dyckHeight (replicate n U) = n := by
  simp [dyckHeight, count_replicate]

lemma dyckHeight_replicate_D (n : ℕ) : dyckHeight (replicate n D) = -n := by
  simp [dyckHeight, count_replicate]

lemma dyckHeight_rotate (w : List DyckStep) (k : ℕ) :
    dyckHeight (w.rotate k) = dyckHeight w := by
  simp [dyckHeight, (w.rotate_perm k).count_eq]

/-- The length of a word in terms of the numbers of its two letters. -/
lemma length_eq_count_add_count (w : List DyckStep) :
    w.length = w.count U + w.count D := by
  induction w with
  | nil => simp
  | cons s w ih => cases s <;> simp [ih] <;> omega

/-! ### Dyck prefixes and Dyck words -/

/-- A word all of whose prefixes have nonnegative height (Coq `Dyck_prefix`). -/
def IsDyckPrefix (w : List DyckStep) : Prop := ∀ i, 0 ≤ dyckHeight (w.take i)

/-- A Dyck word: a Dyck prefix of height `0` (Coq `Dyck_word`). -/
def IsDyckWord (w : List DyckStep) : Prop := IsDyckPrefix w ∧ dyckHeight w = 0

/-- To check a bound on the heights of all the prefixes of `w` it suffices to check it for
the prefixes of length at most `|w|` (Coq `height_take_leq`). -/
lemma forall_take_iff_forall_take_le {h : ℤ} {w : List DyckStep} :
    (∀ i, h ≤ dyckHeight (w.take i)) ↔ ∀ i ≤ w.length, h ≤ dyckHeight (w.take i) := by
  refine ⟨fun H i _ ↦ H i, fun H i ↦ ?_⟩
  rcases le_or_gt i w.length with hi | hi
  · exact H i hi
  · rw [take_of_length_le hi.le, ← take_of_length_le (le_refl w.length)]
    exact H w.length le_rfl

lemma isDyckPrefix_iff {w : List DyckStep} :
    IsDyckPrefix w ↔ ∀ i ≤ w.length, 0 ≤ dyckHeight (w.take i) :=
  forall_take_iff_forall_take_le

@[simp] lemma isDyckWord_nil : IsDyckWord [] := ⟨fun i ↦ by simp, by simp⟩

lemma IsDyckWord.height {w : List DyckStep} (h : IsDyckWord w) : dyckHeight w = 0 := h.2

lemma IsDyckWord.take_nonneg {w : List DyckStep} (h : IsDyckWord w) (i : ℕ) :
    0 ≤ dyckHeight (w.take i) := h.1 i

/-- The concatenation of two Dyck words is a Dyck word (Coq `Dyck_word_cat`). -/
lemma isDyckWord_append {u v : List DyckStep} (hu : IsDyckWord u) (hv : IsDyckWord v) :
    IsDyckWord (u ++ v) := by
  refine ⟨fun i ↦ ?_, by rw [dyckHeight_append, hu.2, hv.2]; ring⟩
  rw [take_append, dyckHeight_append]
  rcases le_or_gt i u.length with hi | hi
  · have h0 : i - u.length = 0 := by omega
    rw [h0]
    simpa using hu.1 i
  · rw [take_of_length_le hi.le, hu.2]
    simpa using hv.1 (i - u.length)

/-- Nesting a Dyck word inside a pair of matching parentheses gives a Dyck word
(Coq `Dyck_word_OwC`). -/
lemma isDyckWord_nest {w : List DyckStep} (h : IsDyckWord w) : IsDyckWord (U :: (w ++ [D])) := by
  constructor
  · intro i
    match i with
    | 0 => simp
    | (i + 1) =>
      rw [take_succ_cons, dyckHeight_cons_U]
      rcases le_or_gt i w.length with hi | hi
      · rw [take_append_of_le_length hi]
        have := h.1 i
        omega
      · rw [take_of_length_le (by simp; omega), dyckHeight_concat_D, h.2]
        omega
  · rw [dyckHeight_cons_U, dyckHeight_concat_D, h.2]
    ring

/-- The standard join `(D₁)D₂` of two Dyck words is a Dyck word (Coq `Dyck_word_OwCw`). -/
lemma isDyckWord_join {u v : List DyckStep} (hu : IsDyckWord u) (hv : IsDyckWord v) :
    IsDyckWord ((U :: u) ++ D :: v) := by
  have h : (U :: u) ++ D :: v = (U :: (u ++ [D])) ++ v := by simp
  rw [h]
  exact isDyckWord_append (isDyckWord_nest hu) hv

/-- A concatenation of Dyck words is a Dyck word (Coq `Dyck_word_flatten`). -/
lemma isDyckWord_flatten {l : List (List DyckStep)} (h : ∀ w ∈ l, IsDyckWord w) :
    IsDyckWord l.flatten := by
  induction l with
  | nil => simp
  | cons w l ih =>
    rw [flatten_cons]
    exact isDyckWord_append (h w (by simp)) (ih fun x hx ↦ h x (by simp [hx]))

/-! ### Dictionary with Mathlib's bundled Dyck words -/

lemma dyckHeight_nonneg_iff (w : List DyckStep) :
    0 ≤ dyckHeight w ↔ w.count D ≤ w.count U := by
  simp only [dyckHeight, sub_nonneg, Nat.cast_le]

lemma dyckHeight_eq_zero_iff (w : List DyckStep) :
    dyckHeight w = 0 ↔ w.count U = w.count D := by
  simp only [dyckHeight, sub_eq_zero, Nat.cast_inj]

/-- The underlying list of a bundled Dyck word is a Dyck word. -/
lemma isDyckWord_toList (p : DyckWord) : IsDyckWord p.toList := by
  refine ⟨fun i ↦ ?_, ?_⟩
  · rw [dyckHeight_nonneg_iff]
    exact p.count_D_le_count_U i
  · rw [dyckHeight_eq_zero_iff]
    exact p.count_U_eq_count_D

/-- The bundled Dyck word attached to a list satisfying `IsDyckWord`. -/
def toDyckWord {w : List DyckStep} (h : IsDyckWord w) : DyckWord where
  toList := w
  count_U_eq_count_D := (dyckHeight_eq_zero_iff w).1 h.2
  count_D_le_count_U i := (dyckHeight_nonneg_iff _).1 (h.1 i)

@[simp] lemma toList_toDyckWord {w : List DyckStep} (h : IsDyckWord w) :
    (toDyckWord h).toList = w := rfl

/-- A word is a Dyck word if and only if it underlies a bundled Dyck word. -/
lemma isDyckWord_iff_exists_dyckWord {w : List DyckStep} :
    IsDyckWord w ↔ ∃ p : DyckWord, p.toList = w :=
  ⟨fun h ↦ ⟨toDyckWord h, rfl⟩, fun ⟨p, hp⟩ ↦ hp ▸ isDyckWord_toList p⟩

/-! ### The standard factorization -/

/-- The standard factorization of a nonempty Dyck word: `D = (D₁)D₂` (Coq `factor_Dyck`). -/
theorem exists_join_of_isDyckWord {w : List DyckStep} (h : IsDyckWord w) (hne : w ≠ []) :
    ∃ u v, IsDyckWord u ∧ IsDyckWord v ∧ w = (U :: u) ++ D :: v := by
  obtain ⟨p, rfl⟩ := isDyckWord_iff_exists_dyckWord.1 h
  have hp : p ≠ 0 := DyckWord.toList_ne_nil.1 hne
  refine ⟨p.insidePart.toList, p.outsidePart.toList, isDyckWord_toList _, isDyckWord_toList _, ?_⟩
  conv_lhs => rw [← DyckWord.nest_insidePart_add_outsidePart hp]
  change ([U] ++ p.insidePart.toList ++ [D]) ++ p.outsidePart.toList = _
  simp

/-- The standard factorization is unique (Coq `join_Dyck_inj`). -/
theorem join_eq_join_iff {u v u' v' : List DyckStep} (hu : IsDyckWord u) (hu' : IsDyckWord u') :
    (U :: u) ++ D :: v = (U :: u') ++ D :: v' ↔ u = u' ∧ v = v' := by
  refine ⟨fun heq ↦ ?_, fun ⟨h1, h2⟩ ↦ by rw [h1, h2]⟩
  have key : ∀ a b a' b' : List DyckStep, IsDyckWord a → IsDyckWord a' →
      a ++ D :: b = a' ++ D :: b' → a.length ≤ a'.length := by
    intro a b a' b' ha ha' heq
    by_contra hlt
    push_neg at hlt
    have h1 : (a' ++ D :: b').take (a'.length + 1) = a' ++ [D] := by
      rw [take_append]
      simp
    have h2 : (a ++ D :: b).take (a'.length + 1) = a.take (a'.length + 1) := by
      rw [take_append]
      have h0 : a'.length + 1 - a.length = 0 := by omega
      rw [h0]
      simp
    rw [heq, h1] at h2
    have h3 := ha.take_nonneg (a'.length + 1)
    rw [← h2, dyckHeight_concat_D, ha'.2] at h3
    omega
  have heq' : u ++ D :: v = u' ++ D :: v' := by simpa using heq
  have hlen : u.length = u'.length :=
    le_antisymm (key u v u' v' hu hu' heq') (key u' v' u v hu' hu heq'.symm)
  obtain ⟨h3, h4⟩ := append_inj heq' hlen
  exact ⟨h3, by simpa using h4⟩

/-! ### Induction on Dyck words -/

/-- The induction principle attached to the standard factorization (Coq `Dyck_ind`). -/
theorem IsDyckWord.induction {P : List DyckStep → Prop} (hnil : P [])
    (hjoin : ∀ u v, IsDyckWord u → IsDyckWord v → P u → P v → P ((U :: u) ++ D :: v))
    {w : List DyckStep} (h : IsDyckWord w) : P w := by
  induction hw : w.length using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    subst hw
    rcases eq_or_ne w [] with rfl | hne
    · exact hnil
    · obtain ⟨u, v, hu, hv, rfl⟩ := exists_join_of_isDyckWord h hne
      refine hjoin u v hu hv (ih u.length ?_ hu rfl) (ih v.length ?_ hv rfl)
      · simp
      · simp
        omega

/-- A Dyck word has even length (Coq `Dyck_size_even`). -/
theorem even_length_of_isDyckWord {w : List DyckStep} (h : IsDyckWord w) : Even w.length := by
  have h1 := (dyckHeight_eq_zero_iff w).1 h.2
  have h2 := length_eq_count_add_count w
  exact ⟨w.count U, by omega⟩

/-- The length of a bundled Dyck word is twice its semilength. -/
lemma length_toList (p : DyckWord) : p.toList.length = 2 * p.semilength := by
  have h := p.count_U_eq_count_D
  have h2 := length_eq_count_add_count p.toList
  simp only [DyckWord.semilength]
  omega

/-! ### The bijection with binary trees -/

/-- Dyck words, as lists, are Mathlib's bundled Dyck words. -/
def isDyckWordEquiv : {w : List DyckStep // IsDyckWord w} ≃ DyckWord where
  toFun w := toDyckWord w.2
  invFun p := ⟨p.toList, isDyckWord_toList p⟩
  left_inv w := rfl
  right_inv p := by ext1; rfl

/-- Dyck words are in bijection with binary trees (Coq `Dyck_of_bintree`, `bintree_of_Dyck`). -/
def isDyckWordEquivTree : {w : List DyckStep // IsDyckWord w} ≃ Tree Unit :=
  isDyckWordEquiv.trans DyckWord.equivTree

/-- The Dyck word attached to a binary tree (Coq `Dyck_of_bintree`). -/
def dyckOfTree (t : Tree Unit) : List DyckStep := (isDyckWordEquivTree.symm t).1

lemma isDyckWord_dyckOfTree (t : Tree Unit) : IsDyckWord (dyckOfTree t) :=
  (isDyckWordEquivTree.symm t).2

lemma dyckOfTree_eq (t : Tree Unit) : dyckOfTree t = (DyckWord.ofTree t).toList := rfl

/-- The Dyck word of a binary tree has twice as many letters as the tree has nodes (Coq
`size_Dyck_of_bintree`). -/
lemma length_dyckOfTree (t : Tree Unit) : (dyckOfTree t).length = 2 * t.numNodes := by
  have h : (DyckWord.ofTree t).semilength = t.numNodes := by
    rw [← DyckWord.numNodes_toTree, DyckWord.toTree_ofTree]
  rw [dyckOfTree_eq, length_toList, h]

/-! ### The number of Dyck words of a given length -/

/-- Dyck words of length `2 * n`, as a subtype of lists, are equivalent to Mathlib's bundled
Dyck words of semilength `n`. -/
def isDyckWordLengthEquiv (n : ℕ) :
    {w : List DyckStep // IsDyckWord w ∧ w.length = 2 * n} ≃
      {p : DyckWord // p.semilength = n} where
  toFun w := ⟨toDyckWord w.2.1, by
    have h := length_toList (toDyckWord w.2.1)
    rw [toList_toDyckWord] at h
    have h2 := w.2.2
    omega⟩
  invFun p := ⟨p.1.toList, isDyckWord_toList _, by rw [length_toList, p.2]⟩
  left_inv w := rfl
  right_inv p := by ext1; rfl

instance instFintypeIsDyckWordLength (n : ℕ) :
    Fintype {w : List DyckStep // IsDyckWord w ∧ w.length = 2 * n} :=
  Fintype.ofEquiv _ (isDyckWordLengthEquiv n).symm

/-- There are `catalan n` Dyck words of length `2 * n` (Coq `card_Dyck_hsz`). -/
theorem card_isDyckWord_length_eq_catalan (n : ℕ) :
    Fintype.card {w : List DyckStep // IsDyckWord w ∧ w.length = 2 * n} = catalan n := by
  rw [Fintype.card_congr (isDyckWordLengthEquiv n)]
  exact DyckWord.card_dyckWord_semilength_eq_catalan n

end List
