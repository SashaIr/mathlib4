/-
Copyright (c) 2026 Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.Shape.Conjugate

/-!
# Inclusion of Young diagrams and skew shapes

A Lean 4 port of the inclusion / skew shape part of `theories/Combi/partition.v`
from [Coq-Combi](https://github.com/math-comp/Coq-Combi).

## Main definitions

* `List.Included inner outer` : the Ferrers diagram of `inner` is contained in
  that of `outer` (Coq `included`).
* `List.diffShape inner outer` : the skew shape `outer / inner` (Coq `diff_shape`).

## Main results

* `List.included_iff` : characterisation of inclusion in terms of parts.
* `List.Included.antisymm` : inclusion is antisymmetric on partitions.
* `List.included_conjPart_iff` : inclusion is preserved and reflected by conjugation.
* `List.sum_diffShape` : the size of a skew shape.
-/

namespace List

open List

/-! ### Inclusion -/

/-- `Included inner outer` means that the Ferrers diagram of `inner` is contained
in the one of `outer` (Coq `included`). -/
def Included : List ℕ → List ℕ → Prop
  | [], _ => True
  | _ :: _, [] => False
  | i0 :: i, o0 :: o => i0 ≤ o0 ∧ Included i o

instance : ∀ (s t : List ℕ), Decidable (Included s t)
  | [], _ => inferInstanceAs (Decidable True)
  | _ :: _, [] => inferInstanceAs (Decidable False)
  | _ :: i, _ :: o => @instDecidableAnd _ _ inferInstance (List.instDecidableIncluded i o)

@[simp] lemma included_nil (t : List ℕ) : Included [] t := trivial

@[simp] lemma included_cons_nil (a : ℕ) (s : List ℕ) : ¬ Included (a :: s) [] := id

@[simp] lemma included_cons_cons {a b : ℕ} {s t : List ℕ} :
    Included (a :: s) (b :: t) ↔ a ≤ b ∧ Included s t := Iff.rfl

/-- A shape is included in itself. -/
@[refl, simp] lemma Included.refl (s : List ℕ) : Included s s := by
  induction s with
  | nil => simp
  | cons a s ih => exact ⟨le_refl a, ih⟩

/-- Coq `size_included`. -/
lemma Included.length_le {s t : List ℕ} (h : Included s t) : s.length ≤ t.length := by
  induction s generalizing t with
  | nil => simp
  | cons a s ih =>
    cases t with
    | nil => exact absurd h (included_cons_nil a s)
    | cons b t => simpa using ih h.2

lemma Included.getD_le {s t : List ℕ} (h : Included s t) (i : ℕ) : s.getD i 0 ≤ t.getD i 0 := by
  induction s generalizing t i with
  | nil => simp
  | cons a s ih =>
    cases t with
    | nil => exact absurd h (included_cons_nil a s)
    | cons b t =>
      cases i with
      | zero => simpa using h.1
      | succ j => simpa using ih h.2 j

/-- Coq `includedP`. -/
lemma included_iff {s t : List ℕ} :
    Included s t ↔ s.length ≤ t.length ∧ ∀ i, s.getD i 0 ≤ t.getD i 0 := by
  refine ⟨fun h => ⟨h.length_le, h.getD_le⟩, ?_⟩
  intro h
  induction s generalizing t with
  | nil => simp
  | cons a s ih =>
    cases t with
    | nil => simp at h
    | cons b t =>
      obtain ⟨hlen, hnth⟩ := h
      refine ⟨by simpa using hnth 0, ih ⟨by simpa using hlen, fun i => by simpa using hnth (i + 1)⟩⟩

/-- Coq `part_includedP`: for partitions, inclusion is pointwise domination. -/
lemma IsPart.included_iff_getD {s t : List ℕ} (hs : IsPart s) :
    Included s t ↔ ∀ i, s.getD i 0 ≤ t.getD i 0 := by
  refine ⟨fun h => h.getD_le, fun h => List.included_iff.2 ⟨?_, h⟩⟩
  by_contra hlt
  push_neg at hlt
  have h1 : 0 < s.getD t.length 0 := hs.getD_pos hlt
  have h2 : t.getD t.length 0 = 0 := List.getD_eq_default _ _ (le_refl _)
  have := h t.length
  omega

lemma Included.trans {s t u : List ℕ} (h1 : Included s t) (h2 : Included t u) : Included s u :=
  included_iff.2 ⟨le_trans h1.length_le h2.length_le,
    fun i => le_trans (h1.getD_le i) (h2.getD_le i)⟩

/-- Coq `sumn_included`. -/
lemma Included.sum_le {s t : List ℕ} (h : Included s t) : s.sum ≤ t.sum := by
  induction s generalizing t with
  | nil => simp
  | cons a s ih =>
    cases t with
    | nil => exact absurd h (included_cons_nil a s)
    | cons b t =>
      simp only [List.sum_cons]
      exact Nat.add_le_add h.1 (ih h.2)

/-- Coq `included_sumnE`. -/
lemma Included.eq_of_sum_eq {s t : List ℕ} (ht : IsPart t) (h : Included s t)
    (hsum : s.sum = t.sum) : s = t := by
  induction s generalizing t with
  | nil => exact (ht.eq_nil_of_sum_eq_zero (by simpa using hsum.symm)).symm
  | cons a s ih =>
    cases t with
    | nil => exact absurd h (included_cons_nil a s)
    | cons b t =>
      obtain ⟨hab, hst⟩ := h
      have hsum' : s.sum ≤ t.sum := hst.sum_le
      simp only [List.sum_cons] at hsum
      have hab' : a = b := by omega
      subst hab'
      rw [ih ht.2 hst (by omega)]

/-- Coq `included_anti`. -/
lemma Included.antisymm {s t : List ℕ} (ht : IsPart t)
    (h1 : Included s t) (h2 : Included t s) : s = t :=
  h1.eq_of_sum_eq ht (le_antisymm h1.sum_le h2.sum_le)

/-- Coq `included_conj_part`. -/
lemma included_conjPart {s t : List ℕ} (hs : IsPart s) (ht : IsPart t) (h : Included s t) :
    Included (conjPart s) (conjPart t) := by
  rw [(isPart_conjPart hs).included_iff_getD]
  intro j
  by_contra hlt
  push_neg at hlt
  -- `(conjPart t) j < (conjPart s) j` means row `(conjPart t) j` of `s` is longer than that of `t`
  have h1 : (conjPart t).getD j 0 < (conjPart s).getD j 0 := hlt
  set i := (conjPart t).getD j 0 with hi
  have hst : InShape s (i, j) := by
    rw [inShape_conjPart hs]
    exact h1
  have hts : ¬ InShape t (i, j) := by
    rw [inShape_conjPart ht]
    simp only [InShape]
    omega
  exact hts (lt_of_lt_of_le hst (h.getD_le i))

/-- Coq `included_conj_partE`. -/
lemma included_conjPart_iff {s t : List ℕ} (hs : IsPart s) (ht : IsPart t) :
    Included s t ↔ Included (conjPart s) (conjPart t) := by
  refine ⟨included_conjPart hs ht, fun h => ?_⟩
  have := included_conjPart (isPart_conjPart hs) (isPart_conjPart ht) h
  rwa [conjPart_conjPart hs, conjPart_conjPart ht] at this

/-! ### Skew shapes -/

/-- The skew shape `outer / inner` (Coq `diff_shape`). -/
def diffShape : List ℕ → List ℕ → List ℕ
  | [], outer => outer
  | _ :: _, [] => []
  | i0 :: i, o0 :: o => (o0 - i0) :: diffShape i o

@[simp] lemma diffShape_nil (outer : List ℕ) : diffShape [] outer = outer := rfl

@[simp] lemma diffShape_cons_cons (i0 o0 : ℕ) (i o : List ℕ) :
    diffShape (i0 :: i) (o0 :: o) = (o0 - i0) :: diffShape i o := rfl

/-- Coq `size_diff_shape`. -/
@[simp] lemma length_diffShape (inner outer : List ℕ) :
    (diffShape inner outer).length = outer.length := by
  induction inner generalizing outer with
  | nil => simp
  | cons a s ih =>
    cases outer with
    | nil => simp [diffShape]
    | cons b t => simp [ih t]

/-- Coq `nth_diff_shape`. -/
lemma getD_diffShape (inner outer : List ℕ) (i : ℕ) :
    (diffShape inner outer).getD i 0 = outer.getD i 0 - inner.getD i 0 := by
  induction inner generalizing outer i with
  | nil => simp
  | cons a s ih =>
    cases outer with
    | nil => simp [diffShape]
    | cons b t =>
      cases i with
      | zero => simp
      | succ j => simpa using ih t j

/-- Coq `diff_shape_eq`. -/
lemma diffShape_self (s : List ℕ) : diffShape s s = List.replicate s.length 0 := by
  induction s with
  | nil => rfl
  | cons a t ih => simp [ih, List.replicate_succ]

/-- Coq `sumn_diff_shape`. -/
lemma sum_diffShape {inner outer : List ℕ} (h : Included inner outer) :
    (diffShape inner outer).sum = outer.sum - inner.sum := by
  induction inner generalizing outer with
  | nil => simp
  | cons a s ih =>
    cases outer with
    | nil => exact absurd h (included_cons_nil a s)
    | cons b t =>
      obtain ⟨hab, hst⟩ := h
      have hsum : s.sum ≤ t.sum := hst.sum_le
      simp only [diffShape_cons_cons, List.sum_cons, ih hst]
      omega

end List
