/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.GetD
public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.Sort

/-!
# Integer partitions and shapes

This file is a Lean 4 port of the core of `theories/Combi/partition.v` from the
Coq library [Coq-Combi](https://github.com/math-comp/Coq-Combi) (F. Hivert et al.,
distributed under the GPL).

Following the Coq development, *shapes* are plain lists of natural numbers
(`List ℕ`), and being a partition is a predicate `Young.IsPart` on such lists:
a list is a partition when it is weakly decreasing and has no zero part.
Everywhere, the `i`-th part of a shape `μ` is `μ.getD i 0`, which is `0` when
`i` is out of range; this matches the `nth 0 μ i` idiom of the Coq sources.

## Main definitions

* `Young.InShape μ (r, c)` : the box `(r, c)` belongs to the diagram of `μ`.
* `Young.IsPart μ` : `μ` is a partition.

## Main results

* `Young.isPart_iff_getD` : the recursive definition agrees with the pointwise one.
* `Young.IsPart.getD_antitone` : the parts are weakly decreasing.
* `Young.isPart_iff_chain` : a partition is a weakly decreasing list without zeroes.
* `Young.IsPart.ext_getD` : two partitions with the same parts are equal.
* `Young.IsPart.length_le_sum`, `Young.IsPart.sum_le_headD_mul_length` : size bounds.

## Implementation notes

Mathlib has two bundled types for the same objects: `YoungDiagram`, and `Nat.Partition n`
for the partitions of a fixed `n`.  Those are the user-facing types, and a result that a
user is expected to quote should be available for them.  The list model of this directory
is the computational layer: the whole development is by induction on shapes and on words,
which is what plain lists are good at.  `Young.IsPart` is by definition the condition
`YoungDiagram.equivListRowLens` uses, so the Young diagram of a partition `μ` is
`YoungDiagram.ofRowLens μ h.sortedGE`; the dictionaries are in
`Mathlib/Combinatorics/Enumerative/Partition/List/YoungDiagram.lean` and (for
`Nat.Partition`) `Mathlib/Combinatorics/Enumerative/Partition/List/Multiset.lean`.
See `docs/Combi.lean` for the overall picture.

Everything of that layer lives in the `Young` namespace; the root `List` namespace is
reserved for statements about lists as such.

## References

* [W. Fulton, *Young tableaux*][fulton1997]
* [I. G. Macdonald, *Symmetric functions and Hall polynomials*][macdonald1995]
* [F. Hivert et al., *Coq-Combi*][hivert-coqcombi]
-/

@[expose] public section

namespace Young

open List

/-! ### Boxes of a shape -/

/-- The box with coordinates `(r, c)` belongs to the shape `μ`, i.e. `c < μ_r`. -/
def InShape (μ : List ℕ) (rc : ℕ × ℕ) : Prop := rc.2 < μ.getD rc.1 0

instance (μ : List ℕ) (rc : ℕ × ℕ) : Decidable (InShape μ rc) :=
  inferInstanceAs (Decidable (_ < _))

@[simp] lemma inShape_nil (rc : ℕ × ℕ) : ¬ InShape [] rc := by
  simp [InShape]

lemma InShape.lt_length {μ : List ℕ} {r c : ℕ} (h : InShape μ (r, c)) : r < μ.length := by
  by_contra hr
  rw [InShape, List.getD_eq_default _ _ (not_lt.1 hr)] at h
  exact absurd h (by simp)

/-! ### Partitions -/

/-- `IsPart μ` states that the list `μ` is an integer partition: it is weakly
decreasing and contains no zero.  This is the condition defining the subtype that
`YoungDiagram.equivListRowLens` identifies with `YoungDiagram`, and the Coq `is_part`
predicate; the recursive description the Coq proofs induct on is `Young.isPart_cons`. -/
def IsPart (μ : List ℕ) : Prop := μ.SortedGE ∧ ∀ x ∈ μ, 0 < x

instance (μ : List ℕ) : Decidable (IsPart μ) := inferInstanceAs (Decidable (_ ∧ _))

/-- A partition, as a weakly decreasing list, is a sorted list in Mathlib's sense. -/
lemma IsPart.sortedGE {μ : List ℕ} (h : IsPart μ) : μ.SortedGE := h.1

/-- A partition has no zero part. -/
lemma IsPart.pos_of_mem {μ : List ℕ} (h : IsPart μ) {i : ℕ} (hi : i ∈ μ) : 0 < i := h.2 i hi

@[simp] lemma isPart_nil : IsPart [] := ⟨List.sortedGE_iff_pairwise.2 (by simp), by simp⟩

@[simp] lemma isPart_cons {s0 : ℕ} {s : List ℕ} :
    IsPart (s0 :: s) ↔ s.headD 1 ≤ s0 ∧ IsPart s := by
  simp only [IsPart, List.sortedGE_iff_pairwise, List.pairwise_cons, List.mem_cons,
    forall_eq_or_imp]
  constructor
  · rintro ⟨⟨hall, hp⟩, hpos, hposs⟩
    refine ⟨?_, hp, hposs⟩
    cases s with
    | nil => simp only [List.headD_nil]; omega
    | cons b t => simpa using hall b (by simp)
  · rintro ⟨hhead, hp, hposs⟩
    have hpos : 0 < s0 := by
      cases s with
      | nil => simp only [List.headD_nil] at hhead; omega
      | cons b t =>
        simp only [List.headD_cons] at hhead
        exact lt_of_lt_of_le (hposs b (by simp)) hhead
    refine ⟨⟨fun b hb => ?_, hp⟩, hpos, hposs⟩
    cases s with
    | nil => simp at hb
    | cons c t =>
      simp only [List.headD_cons] at hhead
      rcases List.mem_cons.1 hb with rfl | hb
      · exact hhead
      · exact le_trans ((List.pairwise_cons.1 hp).1 b hb) hhead

lemma IsPart.of_cons {s0 : ℕ} {s : List ℕ} (h : IsPart (s0 :: s)) : IsPart s :=
  (isPart_cons.1 h).2

/-- The head of a partition is at least its second part. -/
lemma IsPart.headD_le_of_cons {s0 : ℕ} {s : List ℕ} (h : IsPart (s0 :: s)) :
    s.headD 1 ≤ s0 := (isPart_cons.1 h).1

lemma IsPart.tail {μ : List ℕ} (h : IsPart μ) : IsPart μ.tail := by
  cases μ with
  | nil => exact isPart_nil
  | cons a s => exact h.of_cons

/-- A partition has no zero part. -/
lemma IsPart.zero_notMem {μ : List ℕ} (h : IsPart μ) : (0 : ℕ) ∉ μ :=
  fun hc => absurd (h.pos_of_mem hc) (lt_irrefl 0)

/-- A partition has no zero at its head. -/
lemma IsPart.headD_ne_zero {μ : List ℕ} (h : IsPart μ) : μ.headD 1 ≠ 0 := by
  cases μ with
  | nil => simp
  | cons a s => simpa using (h.pos_of_mem (List.mem_cons_self ..)).ne'

lemma IsPart.headD_pos {μ : List ℕ} (h : IsPart μ) (hne : μ ≠ []) : 0 < μ.headD 0 := by
  cases μ with
  | nil => exact absurd rfl hne
  | cons a s =>
    have := h.headD_ne_zero
    simp only [List.headD_cons] at this ⊢
    omega

lemma IsPart.eq_nil_of_headD_eq_zero {μ : List ℕ} (h : IsPart μ) (h0 : μ.headD 0 = 0) :
    μ = [] := by
  by_contra hne
  exact absurd h0 (h.headD_pos hne).ne'

lemma IsPart.getD_pos {μ : List ℕ} (h : IsPart μ) {i : ℕ} (hi : i < μ.length) :
    0 < μ.getD i 0 := by
  rw [List.getD_eq_getElem _ _ hi]
  exact h.pos_of_mem (List.getElem_mem hi)

/-- The parts of a partition decrease by one step. -/
lemma IsPart.getD_succ_le {μ : List ℕ} (h : IsPart μ) (i : ℕ) :
    μ.getD (i + 1) 0 ≤ μ.getD i 0 := by
  induction μ generalizing i with
  | nil => simp
  | cons a s ih =>
    obtain ⟨h1, h2⟩ := isPart_cons.1 h
    cases i with
    | zero =>
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      cases s with
      | nil => simp
      | cons b t => simpa using h1
    | succ j => simpa using ih h2 j

/-- The parts of a partition are weakly decreasing. -/
lemma IsPart.getD_antitone {μ : List ℕ} (h : IsPart μ) {i j : ℕ} (hij : i ≤ j) :
    μ.getD j 0 ≤ μ.getD i 0 := by
  induction j with
  | zero => simp_all
  | succ k ih =>
    rcases Nat.lt_or_ge i (k + 1) with hk | hk
    · exact le_trans (h.getD_succ_le k) (ih (by omega))
    · simp [show i = k + 1 by omega]

/-- A list which decreases pointwise and whose last entry is nonzero is a partition. -/
lemma isPart_of_getD {μ : List ℕ} (hlast : μ.getLastD 1 ≠ 0)
    (h : ∀ i, μ.getD (i + 1) 0 ≤ μ.getD i 0) : IsPart μ := by
  induction μ with
  | nil => exact isPart_nil
  | cons a s ih =>
    refine isPart_cons.2 ⟨?_, ih ?_ fun i ↦ by simpa using h (i + 1)⟩
    · cases s with
      | nil => simp only [List.headD_nil]; simp at hlast; omega
      | cons b t => simpa using h 0
    · cases s with
      | nil => simp
      | cons b t => simpa using hlast

lemma IsPart.getLastD_ne_zero {μ : List ℕ} (h : IsPart μ) : μ.getLastD 1 ≠ 0 := by
  induction μ with
  | nil => simp
  | cons a s ih =>
    cases s with
    | nil =>
      have := h.headD_ne_zero
      simpa using (by simpa using this : ¬ a = 0)
    | cons b t => simpa using ih h.of_cons

/-- The two standard descriptions of a partition agree (Coq `is_partP`). -/
lemma isPart_iff_getD {μ : List ℕ} :
    IsPart μ ↔ μ.getLastD 1 ≠ 0 ∧ ∀ i, μ.getD (i + 1) 0 ≤ μ.getD i 0 :=
  ⟨fun h => ⟨h.getLastD_ne_zero, h.getD_succ_le⟩, fun h => isPart_of_getD h.1 h.2⟩

/-- Coq `is_part_ijP`. -/
lemma isPart_iff_getD_le {μ : List ℕ} :
    IsPart μ ↔ μ.getLastD 1 ≠ 0 ∧ ∀ i j, i ≤ j → μ.getD j 0 ≤ μ.getD i 0 :=
  ⟨fun h => ⟨h.getLastD_ne_zero, fun _ _ hij => h.getD_antitone hij⟩,
   fun h => isPart_of_getD h.1 fun i => h.2 i (i + 1) (Nat.le_succ i)⟩

/-- Coq `is_part_sortedE`: a partition is a weakly decreasing list of nonzero parts. -/
lemma isPart_iff_chain {μ : List ℕ} :
    IsPart μ ↔ List.IsChain (· ≥ ·) μ ∧ (0 : ℕ) ∉ μ := by
  rw [IsPart, List.sortedGE_iff_isChain]
  refine and_congr_right fun _ => ⟨fun h hc => absurd (h 0 hc) (lt_irrefl 0), fun h x hx => ?_⟩
  exact Nat.pos_of_ne_zero fun hc => h (hc ▸ hx)

/-- A convenient pointwise characterisation of partitions: the parts decrease and
the parts inside the list are positive. -/
lemma isPart_iff_getD_pos {μ : List ℕ} :
    IsPart μ ↔ (∀ i, μ.getD (i + 1) 0 ≤ μ.getD i 0) ∧ ∀ i, i < μ.length → 0 < μ.getD i 0 := by
  refine ⟨fun h => ⟨h.getD_succ_le, fun _ hi => h.getD_pos hi⟩,
    fun ⟨hmono, hpos⟩ => isPart_of_getD ?_ hmono⟩
  cases μ with
  | nil => simp
  | cons a s =>
    rw [getLastD_eq_getD (by simp)]
    exact (hpos _ (by simp)).ne'

lemma IsPart.sublist {μ1 μ2 : List ℕ} (hsub : μ1.Sublist μ2) (h : IsPart μ2) :
    IsPart μ1 := by
  rw [isPart_iff_chain] at h ⊢
  exact ⟨List.IsChain.sublist h.1 hsub, fun hc => h.2 (hsub.mem hc)⟩

lemma IsPart.of_append_left {μ1 μ2 : List ℕ} (h : IsPart (μ1 ++ μ2)) : IsPart μ1 :=
  IsPart.sublist (List.sublist_append_left _ _) h

lemma IsPart.of_append_right {μ1 μ2 : List ℕ} (h : IsPart (μ1 ++ μ2)) : IsPart μ2 :=
  IsPart.sublist (List.sublist_append_right _ _) h

/-- Every part is at most the first one. -/
lemma IsPart.le_headD {μ : List ℕ} (h : IsPart μ) {i : ℕ} (hi : i ∈ μ) :
    i ≤ μ.headD 0 := by
  cases μ with
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
lemma IsPart.eq_nil_of_sum_eq_zero {μ : List ℕ} (h : IsPart μ) (hs : μ.sum = 0) : μ = [] := by
  cases μ with
  | nil => rfl
  | cons a s =>
    have ha : a ≠ 0 := by simpa using h.headD_ne_zero
    simp only [List.sum_cons] at hs
    omega

/-- Coq `size_part`: a partition has at most `sumn μ` parts. -/
lemma IsPart.length_le_sum {μ : List ℕ} (h : IsPart μ) : μ.length ≤ μ.sum := by
  induction μ with
  | nil => simp
  | cons a s ih =>
    have ha : 0 < a := Nat.pos_of_ne_zero (by simpa using h.headD_ne_zero)
    have := ih h.of_cons
    simp only [List.length_cons, List.sum_cons]
    omega

/-- Coq `part_sumn_rectangle`: a partition fits into the rectangle
`(number of parts) × (largest part)`. -/
lemma IsPart.sum_le_headD_mul_length {μ : List ℕ} (h : IsPart μ) :
    μ.sum ≤ μ.headD 0 * μ.length := by
  induction μ with
  | nil => simp
  | cons a s ih =>
    have hrec := ih h.of_cons
    have hhead : s.headD 0 ≤ a := by
      cases s with
      | nil => simp
      | cons b t => simpa using h.headD_le_of_cons
    have : s.headD 0 * s.length ≤ a * s.length := Nat.mul_le_mul_right _ hhead
    simp only [List.sum_cons, List.length_cons, List.headD_cons, Nat.mul_succ]
    omega

/-! ### Equality of partitions -/

/-- A list without trailing zero is determined by its sequence of entries. -/
lemma ext_getD_of_getLastD_ne_zero {p q : List ℕ} (hp : p.getLastD 1 ≠ 0) (hq : q.getLastD 1 ≠ 0)
    (h : ∀ i, p.getD i 0 = q.getD i 0) : p = q := by
  have key : ∀ a b : List ℕ, a.getLastD 1 ≠ 0 → (∀ i, a.getD i 0 = b.getD i 0) →
      a.length ≤ b.length := by
    intro a b ha hab
    by_contra! hlt
    have hane : a ≠ [] := fun hc ↦ by simp [hc] at hlt
    have h1 : a.getD (a.length - 1) 0 ≠ 0 := by rwa [← getLastD_eq_getD hane]
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
lemma IsPart.inShape_of_le {μ : List ℕ} (h : IsPart μ) {r c j k : ℕ}
    (hrc : InShape μ (r, c)) (hj : j ≤ r) (hk : k ≤ c) : InShape μ (j, k) :=
  lt_of_le_of_lt hk (lt_of_lt_of_le hrc (h.getD_antitone hj))

end Young
