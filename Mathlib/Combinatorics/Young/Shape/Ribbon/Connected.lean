/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.Shape.Ribbon.Defs
public import Mathlib.Logic.Relation

/-!
# The textbook definition of a ribbon

A Lean 4 port of the textbook characterisation of ribbons of `theories/Combi/skewpart.v`
from [Coq-Combi](https://github.com/math-comp/Coq-Combi).

`Mathlib/Combinatorics/Young/Shape/Ribbon/Defs.lean` defines a ribbon by the *operative* condition
`Young.RibbonOn`: the skew shape occupies an interval of rows, and each row of the outer
shape ends exactly one box to the right of where the previous row of the inner shape
ended.  Textbooks instead define a ribbon (or border strip) as a skew shape which is
**connected** and **contains no `2 × 2` square**.  This file gives those two conditions and
proves that, together with nonemptiness, they characterise the ribbons.

## Main definitions

* `Young.SkewBox inner outer` : the boxes of the skew shape `outer / inner`.
* `Young.Adjacent` : two boxes of the plane share a side.
* `Young.SkewConnected` : any two boxes of the skew shape are joined by a path of boxes
  (Coq `conn4_skew`).
* `Young.HasNoSquare` : the skew shape contains no `2 × 2` square of boxes
  (Coq `has_no_square`).
* `Young.IsRibbon` : the textbook definition — nonempty, connected, and without a `2 × 2`
  square.

## Main results

* `Young.hasNoSquare_iff` : having no `2 × 2` square means `outer_{i+1} ≤ inner_i + 1`.
* `Young.isRibbon_iff_exists_ribbonOn` : **the textbook definition agrees with the
  operative one** (Coq `ribbon_textbook`).

## References

* [I. G. Macdonald, *Symmetric functions and Hall polynomials*][macdonald1995]
* [F. Hivert et al., *Coq-Combi*][hivert-coqcombi]
-/

@[expose] public section

namespace Young

open List

variable {inner outer : List ℕ}

/-! ### Boxes of a skew shape and adjacency -/

/-- The boxes of the skew shape `outer / inner`: those of `outer` that are not in
`inner`. -/
def SkewBox (inner outer : List ℕ) (rc : ℕ × ℕ) : Prop :=
  inner.getD rc.1 0 ≤ rc.2 ∧ rc.2 < outer.getD rc.1 0

@[simp] lemma skewBox_mk (inner outer : List ℕ) (i j : ℕ) :
    SkewBox inner outer (i, j) ↔ inner.getD i 0 ≤ j ∧ j < outer.getD i 0 := Iff.rfl

/-- Two boxes of the plane are adjacent when they share a side. -/
def Adjacent (p q : ℕ × ℕ) : Prop :=
  (p.1 = q.1 ∧ (p.2 + 1 = q.2 ∨ q.2 + 1 = p.2)) ∨
    (p.2 = q.2 ∧ (p.1 + 1 = q.1 ∨ q.1 + 1 = p.1))

lemma adjacent_symm {p q : ℕ × ℕ} (h : Adjacent p q) : Adjacent q p := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1.symm, h2.symm.imp id id⟩
  · exact Or.inr ⟨h1.symm, h2.symm.imp id id⟩

/-- One step of a path inside the skew shape `outer / inner`. -/
def SkewStep (inner outer : List ℕ) (p q : ℕ × ℕ) : Prop :=
  Adjacent p q ∧ SkewBox inner outer p ∧ SkewBox inner outer q

lemma skewStep_symmetric (inner outer : List ℕ) : Std.Symm (SkewStep inner outer) := by
  constructor
  intro _ _ h
  exact ⟨adjacent_symm h.1, h.2.2, h.2.1⟩

/-- Reversing a path of boxes. -/
lemma ReflTransGen.skewStep_symm {p q : ℕ × ℕ}
    (h : Relation.ReflTransGen (SkewStep inner outer) p q) :
    Relation.ReflTransGen (SkewStep inner outer) q p := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.head ⟨adjacent_symm step.1, step.2.2, step.2.1⟩ ih

/-- The skew shape `outer / inner` is connected: any two of its boxes are joined by a path
of boxes, each two consecutive ones sharing a side (Coq `conn4_skew`). -/
def SkewConnected (inner outer : List ℕ) : Prop :=
  ∀ p q, SkewBox inner outer p → SkewBox inner outer q →
    Relation.ReflTransGen (SkewStep inner outer) p q

/-- The skew shape `outer / inner` contains no `2 × 2` square of boxes
(Coq `has_no_square`). -/
def HasNoSquare (inner outer : List ℕ) : Prop :=
  ∀ i j, ¬ (SkewBox inner outer (i, j) ∧ SkewBox inner outer (i, j + 1) ∧
    SkewBox inner outer (i + 1, j) ∧ SkewBox inner outer (i + 1, j + 1))

/-- The textbook definition of a ribbon: a nonempty connected skew shape without a
`2 × 2` square. -/
def IsRibbon (inner outer : List ℕ) : Prop :=
  (∃ p, SkewBox inner outer p) ∧ SkewConnected inner outer ∧ HasNoSquare inner outer

/-- A row of the skew shape is nonempty exactly when the outer shape is longer there. -/
lemma exists_skewBox_row_iff (i : ℕ) :
    (∃ j, SkewBox inner outer (i, j)) ↔ inner.getD i 0 < outer.getD i 0 := by
  constructor
  · rintro ⟨j, hj⟩
    rw [skewBox_mk] at hj
    omega
  · exact fun h => ⟨inner.getD i 0, le_refl _, h⟩

/-! ### Squares -/

/-- For a skew shape of partitions, containing no `2 × 2` square means that each row of
`outer` ends at most one box after the previous row of `inner`. -/
theorem hasNoSquare_iff (hinner : IsPart inner) (houter : IsPart outer) :
    HasNoSquare inner outer ↔ ∀ i, outer.getD (i + 1) 0 ≤ inner.getD i 0 + 1 := by
  constructor
  · intro h i
    by_contra hcon
    push Not at hcon
    have houtI : outer.getD (i + 1) 0 ≤ outer.getD i 0 := houter.getD_succ_le i
    have hinI : inner.getD (i + 1) 0 ≤ inner.getD i 0 := hinner.getD_succ_le i
    refine h i (inner.getD i 0) ⟨?_, ?_, ?_, ?_⟩ <;> rw [skewBox_mk] <;> omega
  · intro h i j hsq
    rw [skewBox_mk] at hsq
    have h1 := hsq.1
    have h4 := hsq.2.2.2
    rw [skewBox_mk] at h4
    have := h i
    omega

/-! ### Paths do not cross a row where the shape is disconnected -/

/-- If no box of row `k` sits directly above a box of row `k + 1`, then a path of boxes
starting at or above row `k` stays at or above row `k`. -/
lemma le_row_of_reflTransGen {k : ℕ}
    (hk : ∀ c, ¬ (SkewBox inner outer (k, c) ∧ SkewBox inner outer (k + 1, c)))
    {p q : ℕ × ℕ} (h : Relation.ReflTransGen (SkewStep inner outer) p q) (hp : p.1 ≤ k) :
    q.1 ≤ k := by
  induction h with
  | refl => exact hp
  | @tail b c _ hstep ih =>
    obtain ⟨b1, b2⟩ := b
    obtain ⟨c1, c2⟩ := c
    obtain ⟨hadj, hb, hc⟩ := hstep
    simp only at ih ⊢
    rcases hadj with ⟨hrow, -⟩ | ⟨hcol, hrows⟩
    · simp only at hrow; omega
    · simp only at hcol
      subst hcol
      rcases hrows with hup | hdown
      · simp only at hup
        rcases Nat.lt_or_ge b1 k with hlt | hge
        · omega
        · obtain rfl : b1 = k := le_antisymm ih hge
          subst hup
          exact absurd ⟨hb, hc⟩ (hk b2)
      · simp only at hdown; omega

/-! ### The two definitions agree -/

/-- Two boxes in the same row of a skew shape are joined by a path. -/
lemma reflTransGen_of_sameRow {i j j' : ℕ} (hj : SkewBox inner outer (i, j))
    (hj' : SkewBox inner outer (i, j')) :
    Relation.ReflTransGen (SkewStep inner outer) (i, j) (i, j') := by
  have key : ∀ a b : ℕ, a ≤ b → SkewBox inner outer (i, a) → SkewBox inner outer (i, b) →
      Relation.ReflTransGen (SkewStep inner outer) (i, a) (i, b) := by
    intro a b hab
    induction b with
    | zero =>
      obtain rfl : a = 0 := by omega
      exact fun _ _ => Relation.ReflTransGen.refl
    | succ n ih =>
      intro ha hb
      rcases Nat.eq_or_lt_of_le hab with rfl | hlt
      · exact Relation.ReflTransGen.refl
      · rw [skewBox_mk] at ha hb
        have hn : SkewBox inner outer (i, n) := by rw [skewBox_mk]; omega
        exact (ih (by omega) (by rw [skewBox_mk]; omega) hn).tail
          ⟨Or.inl ⟨rfl, Or.inl rfl⟩, hn, by rw [skewBox_mk]; omega⟩
  rcases Nat.le_total j j' with hle | hle
  · exact key j j' hle hj hj'
  · exact ReflTransGen.skewStep_symm (key j' j hle hj' hj)

/-- A ribbon in the operative sense is connected. -/
lemma RibbonOn.skewConnected {start stop : ℕ} (hinner : IsPart inner)
    (h : RibbonOn start stop inner outer) : SkewConnected inner outer := by
  have hstartBox : SkewBox inner outer (start, inner.getD start 0) :=
    ⟨le_refl _, h.getD_start_lt⟩
  -- every box lies in a row between `start` and `stop`
  have hrows : ∀ p, SkewBox inner outer p → start ≤ p.1 ∧ p.1 ≤ stop := by
    rintro ⟨i, j⟩ hb
    rw [skewBox_mk] at hb
    have hlt : inner.getD i 0 < outer.getD i 0 := by omega
    simp only
    constructor
    · by_contra hcon
      rw [h.getD_eq_of_lt (by omega)] at hlt; omega
    · by_contra hcon
      rw [h.getD_eq_of_gt (by omega)] at hlt; omega
  -- every box is joined to the first box of the first row
  have key : ∀ n i, i = start + n → i ≤ stop → ∀ j, SkewBox inner outer (i, j) →
      Relation.ReflTransGen (SkewStep inner outer) (i, j) (start, inner.getD start 0) := by
    intro n
    induction n with
    | zero =>
      rintro i rfl - j hb
      simpa using reflTransGen_of_sameRow hb (by simpa using hstartBox)
    | succ m ih =>
      rintro i rfl hle j hb
      rw [show start + (m + 1) = start + m + 1 from by omega] at hb hle ⊢
      have hprev : start + m < stop := by omega
      have hsucc : outer.getD (start + m + 1) 0 = inner.getD (start + m) 0 + 1 :=
        h.getD_succ (by omega) hprev
      have hmono : inner.getD (start + m + 1) 0 ≤ inner.getD (start + m) 0 :=
        hinner.getD_succ_le _
      have hmid : SkewBox inner outer (start + m + 1, inner.getD (start + m) 0) := by
        rw [skewBox_mk]; omega
      have hup : SkewBox inner outer (start + m, inner.getD (start + m) 0) :=
        ⟨le_refl _, getD_lt hinner h (by omega) (by omega)⟩
      have hstep : SkewStep inner outer (start + m + 1, inner.getD (start + m) 0)
          (start + m, inner.getD (start + m) 0) := ⟨Or.inr ⟨rfl, Or.inr rfl⟩, hmid, hup⟩
      exact ((reflTransGen_of_sameRow hb hmid).tail hstep).trans
        (ih (start + m) rfl (by omega) _ hup)
  intro p q hp hq
  obtain ⟨hp1, hp2⟩ := hrows p hp
  obtain ⟨hq1, hq2⟩ := hrows q hq
  refine (key (p.1 - start) p.1 (by omega) hp2 p.2 (by simpa using hp)).trans
    (ReflTransGen.skewStep_symm (key (q.1 - start) q.1 (by omega) hq2 q.2 (by simpa using hq)))

/-- Coq `ribbon_textbook`: for a skew shape of partitions, the textbook definition of a
ribbon — nonempty, connected and without a `2 × 2` square — agrees with the operative
one. -/
theorem isRibbon_iff_exists_ribbonOn (hinner : IsPart inner) (houter : IsPart outer)
    (hincl : Included inner outer) :
    IsRibbon inner outer ↔ ∃ start stop, RibbonOn start stop inner outer := by
  classical
  constructor
  · rintro ⟨⟨p, hp⟩, hconn, hsq⟩
    rw [hasNoSquare_iff hinner houter] at hsq
    set S := (Finset.range outer.length).filter (fun i ↦ inner.getD i 0 < outer.getD i 0) with hS
    have hmem : ∀ i, i ∈ S ↔ inner.getD i 0 < outer.getD i 0 := by
      intro i
      simp only [hS, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
      intro hlt
      by_contra hcon
      rw [List.getD_eq_default outer 0 (by omega)] at hlt
      omega
    have hpS : p.1 ∈ S := (hmem p.1).2 (by have h1 := hp.1; have h2 := hp.2; omega)
    have hne : S.Nonempty := ⟨p.1, hpS⟩
    have hminBox : SkewBox inner outer (S.min' hne, inner.getD (S.min' hne) 0) :=
      ⟨le_refl _, (hmem _).1 (S.min'_mem hne)⟩
    have hmaxBox : SkewBox inner outer (S.max' hne, inner.getD (S.max' hne) 0) :=
      ⟨le_refl _, (hmem _).1 (S.max'_mem hne)⟩
    refine ⟨S.min' hne, S.max' hne, ?_, ?_, ?_, ?_⟩
    · intro i hi
      refine le_antisymm ?_ (hincl.getD_le i)
      by_contra hcon
      exact absurd (S.le_max' i ((hmem i).2 (by omega))) (by omega)
    · intro i h1 h2
      refine le_antisymm (hsq i) ?_
      by_contra hcon
      have hk : ∀ c, ¬ (SkewBox inner outer (i, c) ∧ SkewBox inner outer (i + 1, c)) := by
        rintro c ⟨hc1, hc2⟩
        rw [skewBox_mk] at hc1 hc2
        omega
      exact absurd (le_row_of_reflTransGen hk (hconn _ _ hminBox hmaxBox) (by simpa using h1))
        (by simp only; omega)
    · exact (hmem _).1 (S.min'_mem hne)
    · intro i hi
      refine le_antisymm ?_ (hincl.getD_le i)
      by_contra hcon
      exact absurd (S.min'_le i ((hmem i).2 (by omega))) (by omega)
  · rintro ⟨start, stop, h⟩
    refine ⟨⟨(start, inner.getD start 0), le_refl _, h.getD_start_lt⟩,
      h.skewConnected hinner, ?_⟩
    rw [hasNoSquare_iff hinner houter]
    intro i
    rcases Nat.lt_or_ge i start with hi | hi
    · have h1 : outer.getD (i + 1) 0 ≤ outer.getD i 0 := houter.getD_succ_le i
      rw [h.getD_eq_of_lt hi] at h1
      omega
    · rcases Nat.lt_or_ge i stop with hi' | hi'
      · rw [h.getD_succ hi hi']
      · rw [h.getD_eq_of_gt (by omega)]
        have := hinner.getD_succ_le i
        omega

end Young
