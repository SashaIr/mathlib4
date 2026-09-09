/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.GetD

/-!
# Integer partitions and shapes

This file is a Lean 4 port of the core of `theories/Combi/partition.v` from the
Coq library [Coq-Combi](https://github.com/math-comp/Coq-Combi) (F. Hivert et al.,
distributed under the GPL).

Following the Coq development, *shapes* are plain lists of natural numbers
(`List ℕ`), and being a partition is a predicate `List.IsPart` on such lists:
a list is a partition when it is weakly decreasing and has no zero part.
Everywhere, the `i`-th part of a shape `sh` is `sh.getD i 0`, which is `0` when
`i` is out of range; this matches the `nth 0 sh i` idiom of the Coq sources.

## Main definitions

* `List.InShape sh (r, c)` : the box `(r, c)` belongs to the diagram of `sh`.
* `List.IsPart sh` : `sh` is a partition.

## Main results

* `List.isPart_iff_getD` : the recursive definition agrees with the pointwise one.
* `List.IsPart.getD_antitone` : the parts are weakly decreasing.
* `List.isPart_iff_chain` : a partition is a weakly decreasing list without zeroes.
* `List.IsPart.ext_getD` : two partitions with the same parts are equal.
* `List.IsPart.length_le_sum`, `List.IsPart.sum_le_headD_mul_length` : size bounds.
-/

@[expose] public section

namespace List

open List

/-! ### Boxes of a shape -/

/-- The box with coordinates `(r, c)` belongs to the shape `sh`, i.e. `c < sh_r`. -/
def InShape (sh : List ℕ) (rc : ℕ × ℕ) : Prop := rc.2 < sh.getD rc.1 0

instance (sh : List ℕ) (rc : ℕ × ℕ) : Decidable (InShape sh rc) :=
  inferInstanceAs (Decidable (_ < _))

@[simp] lemma inShape_nil (rc : ℕ × ℕ) : ¬ InShape [] rc := by
  simp [InShape]

lemma InShape.lt_length {sh : List ℕ} {r c : ℕ} (h : InShape sh (r, c)) : r < sh.length := by
  by_contra hr
  rw [InShape, List.getD_eq_default _ _ (not_lt.1 hr)] at h
  exact absurd h (by simp)

/-! ### Partitions -/

/-- `IsPart sh` states that the list `sh` is an integer partition: it is weakly
decreasing and contains no zero.  This is the Coq `is_part` predicate. -/
def IsPart : List ℕ → Prop
  | [] => True
  | s0 :: s => s.headD 1 ≤ s0 ∧ IsPart s

instance : ∀ sh : List ℕ, Decidable (IsPart sh)
  | [] => inferInstanceAs (Decidable True)
  | _ :: s => @instDecidableAnd _ _ inferInstance (List.instDecidableIsPart s)

@[simp] lemma isPart_nil : IsPart [] := trivial

@[simp] lemma isPart_cons {s0 : ℕ} {s : List ℕ} :
    IsPart (s0 :: s) ↔ s.headD 1 ≤ s0 ∧ IsPart s := Iff.rfl

lemma IsPart.of_cons {s0 : ℕ} {s : List ℕ} (h : IsPart (s0 :: s)) : IsPart s := h.2

lemma IsPart.tail {sh : List ℕ} (h : IsPart sh) : IsPart sh.tail := by
  cases sh with
  | nil => exact isPart_nil
  | cons a s => exact h.2

/-- A partition has no zero at its head. -/
lemma IsPart.headD_ne_zero {sh : List ℕ} (h : IsPart sh) : sh.headD 1 ≠ 0 := by
  induction sh with
  | nil => simp
  | cons a s ih =>
    obtain ⟨h1, h2⟩ := h
    have := ih h2
    simp only [List.headD_cons]
    cases s with
    | nil => simp only [List.headD_nil] at h1; omega
    | cons b t => simp only [List.headD_cons] at h1 this ⊢; omega

/-- A partition has no zero part. -/
lemma IsPart.zero_notMem {sh : List ℕ} (h : IsPart sh) : (0 : ℕ) ∉ sh := by
  induction sh with
  | nil => simp
  | cons a s ih =>
    have ha : a ≠ 0 := by
      have := (IsPart.headD_ne_zero (sh := a :: s) h)
      simp only [List.headD_cons] at this
      exact this
    simp only [List.mem_cons, not_or]
    exact ⟨fun hc => ha hc.symm, ih h.2⟩

lemma IsPart.headD_pos {sh : List ℕ} (h : IsPart sh) (hne : sh ≠ []) : 0 < sh.headD 0 := by
  cases sh with
  | nil => exact absurd rfl hne
  | cons a s =>
    have := h.headD_ne_zero
    simp only [List.headD_cons] at this ⊢
    omega

lemma IsPart.eq_nil_of_headD_eq_zero {sh : List ℕ} (h : IsPart sh) (h0 : sh.headD 0 = 0) :
    sh = [] := by
  by_contra hne
  exact absurd h0 (h.headD_pos hne).ne'

lemma IsPart.pos_of_mem {sh : List ℕ} (h : IsPart sh) {i : ℕ} (hi : i ∈ sh) : 0 < i :=
  Nat.pos_of_ne_zero fun hc => h.zero_notMem (hc ▸ hi)

lemma IsPart.getD_pos {sh : List ℕ} (h : IsPart sh) {i : ℕ} (hi : i < sh.length) :
    0 < sh.getD i 0 := by
  rw [List.getD_eq_getElem _ _ hi]
  exact h.pos_of_mem (List.getElem_mem hi)

/-- The parts of a partition decrease by one step. -/
lemma IsPart.getD_succ_le {sh : List ℕ} (h : IsPart sh) (i : ℕ) :
    sh.getD (i + 1) 0 ≤ sh.getD i 0 := by
  induction sh generalizing i with
  | nil => simp
  | cons a s ih =>
    obtain ⟨h1, h2⟩ := h
    cases i with
    | zero =>
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      cases s with
      | nil => simp
      | cons b t => simpa using h1
    | succ j => simpa using ih h2 j

/-- The parts of a partition are weakly decreasing. -/
lemma IsPart.getD_antitone {sh : List ℕ} (h : IsPart sh) {i j : ℕ} (hij : i ≤ j) :
    sh.getD j 0 ≤ sh.getD i 0 := by
  induction j with
  | zero => simp_all
  | succ k ih =>
    rcases Nat.lt_or_ge i (k + 1) with hk | hk
    · exact le_trans (h.getD_succ_le k) (ih (by omega))
    · simp [show i = k + 1 by omega]

/-- A list which decreases pointwise and whose last entry is nonzero is a partition. -/
lemma isPart_of_getD {sh : List ℕ} (hlast : sh.getLastD 1 ≠ 0)
    (h : ∀ i, sh.getD (i + 1) 0 ≤ sh.getD i 0) : IsPart sh := by
  induction sh with
  | nil => exact isPart_nil
  | cons a s ih =>
    refine ⟨?_, ih ?_ fun i ↦ by simpa using h (i + 1)⟩
    · cases s with
      | nil => simp only [List.headD_nil]; simp at hlast; omega
      | cons b t => simpa using h 0
    · cases s with
      | nil => simp
      | cons b t => simpa using hlast

lemma IsPart.getLastD_ne_zero {sh : List ℕ} (h : IsPart sh) : sh.getLastD 1 ≠ 0 := by
  induction sh with
  | nil => simp
  | cons a s ih =>
    cases s with
    | nil =>
      have := h.headD_ne_zero
      simpa using (by simpa using this : ¬ a = 0)
    | cons b t => simpa using ih h.2

/-- The two standard descriptions of a partition agree (Coq `is_partP`). -/
lemma isPart_iff_getD {sh : List ℕ} :
    IsPart sh ↔ sh.getLastD 1 ≠ 0 ∧ ∀ i, sh.getD (i + 1) 0 ≤ sh.getD i 0 :=
  ⟨fun h => ⟨h.getLastD_ne_zero, h.getD_succ_le⟩, fun h => isPart_of_getD h.1 h.2⟩

/-- Coq `is_part_ijP`. -/
lemma isPart_iff_getD_le {sh : List ℕ} :
    IsPart sh ↔ sh.getLastD 1 ≠ 0 ∧ ∀ i j, i ≤ j → sh.getD j 0 ≤ sh.getD i 0 :=
  ⟨fun h => ⟨h.getLastD_ne_zero, fun _ _ hij => h.getD_antitone hij⟩,
   fun h => isPart_of_getD h.1 fun i => h.2 i (i + 1) (Nat.le_succ i)⟩

/-- Coq `is_part_sortedE`: a partition is a weakly decreasing list of nonzero parts. -/
lemma isPart_iff_chain {sh : List ℕ} :
    IsPart sh ↔ List.IsChain (· ≥ ·) sh ∧ (0 : ℕ) ∉ sh := by
  refine ⟨fun h ↦ ⟨?_, h.zero_notMem⟩, ?_⟩
  · induction sh with
    | nil => exact List.IsChain.nil
    | cons a s ih =>
      obtain ⟨h1, h2⟩ := h
      cases s with
      | nil => exact List.IsChain.singleton _
      | cons b t => exact List.IsChain.cons_cons (by simpa using h1) (ih h2)
  · rintro ⟨hchain, h0⟩
    induction sh with
    | nil => exact isPart_nil
    | cons a s ih =>
      cases s with
      | nil =>
        refine ⟨?_, isPart_nil⟩
        simp only [List.headD_nil]
        have : (0 : ℕ) ≠ a := by simpa using h0
        omega
      | cons b t =>
        obtain ⟨hab, hrest⟩ := List.isChain_cons_cons.1 hchain
        refine ⟨by simpa using hab, ih hrest ?_⟩
        simp only [List.mem_cons, not_or] at h0 ⊢
        exact h0.2

lemma getLastD_eq_getD {sh : List ℕ} (d : ℕ) (h : sh ≠ []) :
    sh.getLastD d = sh.getD (sh.length - 1) 0 := by
  induction sh generalizing d with
  | nil => simp at h
  | cons a s ih =>
    cases s with
    | nil => simp
    | cons b t =>
      rw [List.getLastD_cons, ih a (by simp)]
      simp

/-- A convenient pointwise characterisation of partitions: the parts decrease and
the parts inside the list are positive. -/
lemma isPart_iff_getD_pos {sh : List ℕ} :
    IsPart sh ↔ (∀ i, sh.getD (i + 1) 0 ≤ sh.getD i 0) ∧ ∀ i, i < sh.length → 0 < sh.getD i 0 := by
  refine ⟨fun h => ⟨h.getD_succ_le, fun _ hi => h.getD_pos hi⟩,
    fun ⟨hmono, hpos⟩ => isPart_of_getD ?_ hmono⟩
  cases sh with
  | nil => simp
  | cons a s =>
    rw [getLastD_eq_getD 1 (by simp)]
    exact (hpos _ (by simp)).ne'

lemma IsPart.sublist {sh1 sh2 : List ℕ} (hsub : sh1.Sublist sh2) (h : IsPart sh2) :
    IsPart sh1 := by
  rw [isPart_iff_chain] at h ⊢
  exact ⟨List.IsChain.sublist h.1 hsub, fun hc => h.2 (hsub.mem hc)⟩

lemma IsPart.of_append_left {sh1 sh2 : List ℕ} (h : IsPart (sh1 ++ sh2)) : IsPart sh1 :=
  IsPart.sublist (List.sublist_append_left _ _) h

lemma IsPart.of_append_right {sh1 sh2 : List ℕ} (h : IsPart (sh1 ++ sh2)) : IsPart sh2 :=
  IsPart.sublist (List.sublist_append_right _ _) h

/-- Every part is at most the first one. -/
lemma IsPart.le_headD {sh : List ℕ} (h : IsPart sh) {i : ℕ} (hi : i ∈ sh) :
    i ≤ sh.headD 0 := by
  cases sh with
  | nil => simp at hi
  | cons a s =>
    simp only [List.headD_cons]
    rcases List.mem_cons.1 hi with rfl | hi
    · exact le_refl _
    · obtain ⟨n, hn, hval⟩ := List.getElem_of_mem hi
      have hle : (a :: s).getD (n + 1) 0 ≤ (a :: s).getD 0 0 :=
        h.getD_antitone (Nat.zero_le _)
      rw [List.getD_cons_succ, List.getD_cons_zero, List.getD_eq_getElem _ _ hn, hval] at hle
      exact hle

/-! ### Partitions and sums -/

/-- Coq `part0`: the only partition of `0` is the empty one. -/
lemma IsPart.eq_nil_of_sum_eq_zero {sh : List ℕ} (h : IsPart sh) (hs : sh.sum = 0) : sh = [] := by
  cases sh with
  | nil => rfl
  | cons a s =>
    have ha : a ≠ 0 := by simpa using h.headD_ne_zero
    simp only [List.sum_cons] at hs
    omega

/-- Coq `size_part`: a partition has at most `sumn sh` parts. -/
lemma IsPart.length_le_sum {sh : List ℕ} (h : IsPart sh) : sh.length ≤ sh.sum := by
  induction sh with
  | nil => simp
  | cons a s ih =>
    have ha : 0 < a := Nat.pos_of_ne_zero (by simpa using h.headD_ne_zero)
    have := ih h.2
    simp only [List.length_cons, List.sum_cons]
    omega

/-- Coq `part_sumn_rectangle`: a partition fits into the rectangle
`(number of parts) × (largest part)`. -/
lemma IsPart.sum_le_headD_mul_length {sh : List ℕ} (h : IsPart sh) :
    sh.sum ≤ sh.headD 0 * sh.length := by
  induction sh with
  | nil => simp
  | cons a s ih =>
    have hrec := ih h.2
    have hhead : s.headD 0 ≤ a := by
      cases s with
      | nil => simp
      | cons b t => simpa using h.1
    have : s.headD 0 * s.length ≤ a * s.length := Nat.mul_le_mul_right _ hhead
    simp only [List.sum_cons, List.length_cons, List.headD_cons, Nat.mul_succ]
    omega

/-- Coq `leq_head_sumn`. -/
lemma headD_le_sum (sh : List ℕ) : sh.headD 0 ≤ sh.sum := by
  cases sh with
  | nil => simp
  | cons a s => simp

/-! ### Equality of partitions -/

/-- A list without trailing zero is determined by its sequence of entries. -/
lemma ext_getD_of_getLastD_ne_zero {p q : List ℕ} (hp : p.getLastD 1 ≠ 0) (hq : q.getLastD 1 ≠ 0)
    (h : ∀ i, p.getD i 0 = q.getD i 0) : p = q := by
  have key : ∀ a b : List ℕ, a.getLastD 1 ≠ 0 → (∀ i, a.getD i 0 = b.getD i 0) →
      a.length ≤ b.length := by
    intro a b ha hab
    by_contra! hlt
    have hane : a ≠ [] := fun hc ↦ by simp [hc] at hlt
    have h1 : a.getD (a.length - 1) 0 ≠ 0 := by rwa [← getLastD_eq_getD 1 hane]
    have h2 : b.getD (a.length - 1) 0 = 0 := List.getD_eq_default _ _ (by omega)
    exact h1 (by rw [hab, h2])
  have hlen : p.length = q.length :=
    le_antisymm (key p q hp h) (key q p hq fun i => (h i).symm)
  apply List.ext_getElem hlen
  intro i hi hi'
  have := h i
  rwa [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi'] at this

/-- Coq `part_eqP`: two partitions with the same parts are equal. -/
lemma IsPart.ext_getD {p q : List ℕ} (hp : IsPart p) (hq : IsPart q)
    (h : ∀ i, p.getD i 0 = q.getD i 0) : p = q :=
  ext_getD_of_getLastD_ne_zero hp.getLastD_ne_zero hq.getLastD_ne_zero h

/-! ### Boxes of a partition -/

/-- Coq `in_part_le`: the diagram of a partition is a lower set. -/
lemma IsPart.inShape_of_le {sh : List ℕ} (h : IsPart sh) {r c j k : ℕ}
    (hrc : InShape sh (r, c)) (hj : j ≤ r) (hk : k ≤ c) : InShape sh (j, k) :=
  lt_of_le_of_lt hk (lt_of_lt_of_le hrc (h.getD_antitone hj))

end List
