/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Group.List.GetD
public import Mathlib.Combinatorics.Young.HookLength.Basic
public import Mathlib.Combinatorics.Young.Shape.Corners
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-!
# The hook walk

This file contains the probabilistic ingredient of the Greene–Nijenhuis–Wilf proof of the
hook length formula (the Coq file `HookFormula/hook.v`).

The *hook walk* on a Young diagram `η` starts at a box and, from a box `(i, j)` whose hook
contains more than one box, jumps to one of the `hookLength η i j - 1` other boxes of the
hook of `(i, j)`, all of them being equally likely; the walk stops when it reaches a box
whose hook is reduced to itself, that is a removable corner of `η`.

`hookWalkProb η c x` is the probability that the walk started at the box `x` stops at the
box `c`; it is defined by well-founded recursion, the walk moving to boxes with larger
coordinates.

## Main definitions

* `Young.hookWalkProb η c x` : the probability that the hook walk started at the box `x`
  of `η` ends at the box `c`.

## Main results

* `Young.hookWalkProb_eq_zero_of_not_le` : the walk cannot reach a box that is not weakly
  below and to the right of the starting box.
* `Young.sum_hookWalkProb_corners` : the walk ends at a corner with probability one.
* `Young.hookWalkProb_corner` : **the Greene–Nijenhuis–Wilf formula** for the probability of
  ending at a given corner `(al, be)`, starting from a box `(a, b)` with `a ≤ al` and
  `b ≤ be`.

## References

* [C. Greene, A. Nijenhuis and H. S. Wilf, *A probabilistic proof of a formula for the
  number of Young tableaux of a given shape*][greene-nijenhuis-wilf1979]
* [F. Hivert et al., *Coq-Combi*][hivert-coqcombi]
-/

@[expose] public section

namespace Young

open List Finset

/-! ### Two auxiliary lemmas -/

/-- A telescoping sum: for `b ≤ m`, the sum of `f a * ∏_{a < i < m} (1 + f i)` over the
`a ∈ [b, m]` is `∏_{b ≤ i < m} (1 + f i) + f m - 1`. -/
lemma sum_Icc_mul_prod_Ioo (f : ℕ → ℚ) (m : ℕ) :
    ∀ (k b : ℕ), b + k = m → ∑ a ∈ Finset.Icc b m, f a * ∏ i ∈ Finset.Ioo a m, (1 + f i)
      = (∏ i ∈ Finset.Ico b m, (1 + f i)) + f m - 1 := by
  intro k
  induction k with
  | zero => rintro b rfl; simp
  | succ k ih =>
    intro b hb
    have hlt : b < m := by omega
    have hIcc : Finset.Icc b m = insert b (Finset.Icc (b + 1) m) := by
      ext a; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hIco : Finset.Ico b m = insert b (Finset.Ico (b + 1) m) := by
      ext a; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    rw [hIcc, Finset.sum_insert (by simp), ih (b + 1) (by omega),
      show Finset.Ioo b m = Finset.Ico (b + 1) m from rfl, hIco,
      Finset.prod_insert (by simp)]
    ring

/-! ### The hook walk -/

/-- The probability that the hook walk of the diagram `η` started at the box `x` ends at
the box `c`.  From a box whose hook has more than one box, the walk jumps uniformly to one of
the other boxes of its hook; the boxes with a hook of length one, at which the walk stops,
are exactly the removable corners. -/
def hookWalkProb (η : List ℕ) (c : ℕ × ℕ) (x : ℕ × ℕ) : ℚ :=
  if hookLength η x.1 x.2 ≤ 1 then (if x = c then 1 else 0)
  else
    ((∑ j ∈ (Finset.Ioo x.2 (η.getD x.1 0)).attach, hookWalkProb η c (x.1, j.1)) +
      (∑ i ∈ (Finset.Ioo x.1 ((conjPart η).getD x.2 0)).attach, hookWalkProb η c (i.1, x.2)))
      / ((hookLength η x.1 x.2 : ℚ) - 1)
termination_by (η.sum - x.1) + (η.sum - x.2)
decreasing_by
  · have hj := j.2
    have h1 : η.getD x.1 0 ≤ η.sum := getD_le_sum _ _
    rw [Finset.mem_Ioo] at hj
    omega
  · have hi := i.2
    have h2 : (conjPart η).getD x.2 0 ≤ η.sum := by
      simpa using getD_le_sum (conjPart η) x.2
    rw [Finset.mem_Ioo] at hi
    omega

/-- The walk stops at a box whose hook is reduced to a single box. -/
lemma hookWalkProb_of_le {η : List ℕ} {c x : ℕ × ℕ} (h : hookLength η x.1 x.2 ≤ 1) :
    hookWalkProb η c x = if x = c then 1 else 0 := by
  rw [hookWalkProb, ite_eq_left h]

/-- The recursive step of the hook walk. -/
lemma hookWalkProb_of_lt {η : List ℕ} {c x : ℕ × ℕ} (h : 1 < hookLength η x.1 x.2) :
    hookWalkProb η c x =
      ((∑ j ∈ Finset.Ioo x.2 (η.getD x.1 0), hookWalkProb η c (x.1, j)) +
        (∑ i ∈ Finset.Ioo x.1 ((conjPart η).getD x.2 0), hookWalkProb η c (i, x.2)))
        / ((hookLength η x.1 x.2 : ℚ) - 1) := by
  rw [hookWalkProb, ite_eq_right (by omega),
    Finset.sum_attach _ (fun j => hookWalkProb η c (x.1, j)),
    Finset.sum_attach _ (fun i => hookWalkProb η c (i, x.2))]

/-! ### Hook lengths of the boxes of a diagram -/

variable {η : List ℕ}

/-- The hook length of a box, as the number of boxes of its arm plus its leg plus one. -/
lemma hookLength_add_one (hη : IsPart η) {i j : ℕ} (hc : j < η.getD i 0) :
    hookLength η i j + 1 = (η.getD i 0 - j) + ((conjPart η).getD j 0 - i) := by
  have h1 : i < (conjPart η).getD j 0 := lt_getD_conjPart hη hc
  simp only [hookLength]
  omega

/-- The number of boxes to which the walk may jump from a box is the hook length minus one. -/
lemma card_hook_moves (hη : IsPart η) {i j : ℕ} (hc : j < η.getD i 0) :
    (Finset.Ioo j (η.getD i 0)).card + (Finset.Ioo i ((conjPart η).getD j 0)).card
      = hookLength η i j - 1 := by
  have h1 : i < (conjPart η).getD j 0 := lt_getD_conjPart hη hc
  have h2 := hookLength_add_one hη hc
  rw [Nat.card_Ioo, Nat.card_Ioo]
  omega

/-- A box has hook length one exactly when it is a removable corner. -/
lemma hookLength_eq_one_iff (hη : IsPart η) {i j : ℕ} (hc : j < η.getD i 0) :
    hookLength η i j = 1 ↔ IsRemCorner η i ∧ j = η.getD i 0 - 1 := by
  have h1 : i < (conjPart η).getD j 0 := lt_getD_conjPart hη hc
  have h2 := hookLength_add_one hη hc
  constructor
  · intro h
    have hj : η.getD i 0 = j + 1 := by omega
    have hcj : (conjPart η).getD j 0 = i + 1 := by omega
    have : η.getD (i + 1) 0 ≤ j := by
      rw [getD_le_conjPart_iff hη]
      omega
    exact ⟨by simp only [IsRemCorner]; omega, by omega⟩
  · rintro ⟨hcorner, rfl⟩
    have : η.getD (i + 1) 0 ≤ η.getD i 0 - 1 := by
      simp only [IsRemCorner] at hcorner
      omega
    have hle : (conjPart η).getD (η.getD i 0 - 1) 0 ≤ i + 1 :=
      (getD_le_conjPart_iff hη _ _).1 this
    omega

/-- Outside of the diagram, the walk has already stopped. -/
lemma hookLength_le_one_of_sum_le {i j : ℕ} (h1 : η.sum ≤ i) (h2 : η.sum ≤ j) :
    hookLength η i j ≤ 1 := by
  have ha : η.getD i 0 ≤ η.sum := getD_le_sum _ _
  have hb : (conjPart η).getD j 0 ≤ η.sum := by
    simpa using getD_le_sum (conjPart η) j
  simp only [hookLength]
  omega

/-! ### The walk moves to the right and downwards -/

private lemma hookWalkProb_eq_zero_aux (c : ℕ × ℕ) :
    ∀ (N : ℕ) (x : ℕ × ℕ), (η.sum - x.1) + (η.sum - x.2) ≤ N →
      ¬ (x.1 ≤ c.1 ∧ x.2 ≤ c.2) → hookWalkProb η c x = 0 := by
  intro N
  induction N with
  | zero =>
    intro x hx hnot
    rw [hookWalkProb_of_le (hookLength_le_one_of_sum_le (by omega) (by omega)), ite_eq_right]
    rintro rfl
    exact hnot ⟨le_rfl, le_rfl⟩
  | succ N ih =>
    intro x hx hnot
    by_cases h : hookLength η x.1 x.2 ≤ 1
    · rw [hookWalkProb_of_le h, ite_eq_right]
      rintro rfl
      exact hnot ⟨le_rfl, le_rfl⟩
    · rw [hookWalkProb_of_lt (by omega)]
      have hrow : ∀ j ∈ Finset.Ioo x.2 (η.getD x.1 0), hookWalkProb η c (x.1, j) = 0 := by
        intro j hj
        rw [Finset.mem_Ioo] at hj
        have hle : η.getD x.1 0 ≤ η.sum := getD_le_sum _ _
        refine ih (x.1, j) (by simp only; omega) ?_
        simp only
        omega
      have hcol : ∀ i ∈ Finset.Ioo x.1 ((conjPart η).getD x.2 0),
          hookWalkProb η c (i, x.2) = 0 := by
        intro i hi
        rw [Finset.mem_Ioo] at hi
        have hle : (conjPart η).getD x.2 0 ≤ η.sum := by
          simpa using getD_le_sum (conjPart η) x.2
        refine ih (i, x.2) (by simp only; omega) ?_
        simp only
        omega
      rw [Finset.sum_congr rfl hrow, Finset.sum_congr rfl hcol]
      simp

/-- The hook walk cannot reach a box which is not weakly below and to the right of the
starting box. -/
lemma hookWalkProb_eq_zero_of_not_le {c x : ℕ × ℕ} (h : ¬ (x.1 ≤ c.1 ∧ x.2 ≤ c.2)) :
    hookWalkProb η c x = 0 :=
  hookWalkProb_eq_zero_aux c _ x le_rfl h

/-! ### The walk ends at a corner -/

/-- A box of the diagram to which the walk may jump from a box of the diagram is again a box
of the diagram. -/
lemma lt_getD_of_lt_getD_conjPart (hη : IsPart η) {i j : ℕ}
    (h : i < (conjPart η).getD j 0) : j < η.getD i 0 := by
  by_contra hcon
  exact absurd ((getD_le_conjPart_iff hη i j).1 (by omega)) (by omega)

private lemma sum_hookWalkProb_corners_aux (hη : IsPart η) :
    ∀ (N i j : ℕ), (η.sum - i) + (η.sum - j) ≤ N → j < η.getD i 0 →
      ∑ r ∈ Finset.range η.length,
        (if IsRemCorner η r then hookWalkProb η (r, η.getD r 0 - 1) (i, j) else 0) = 1 := by
  have base : ∀ i j : ℕ, j < η.getD i 0 → hookLength η i j ≤ 1 →
      ∑ r ∈ Finset.range η.length,
        (if IsRemCorner η r then hookWalkProb η (r, η.getD r 0 - 1) (i, j) else 0) = 1 := by
    intro i j hc h
    have h1 : hookLength η i j = 1 := le_antisymm h (one_le_hookLength hη hc)
    obtain ⟨hcorner, hj⟩ := (hookLength_eq_one_iff hη hc).1 h1
    have hilen : i < η.length := by
      by_contra hcon
      rw [List.getD_eq_default _ _ (by omega)] at hc
      omega
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_range.2 hilen) ?_]
    · rw [ite_eq_left hcorner, hookWalkProb_of_le h, ite_eq_left (by rw [hj])]
    · intro r _ hne
      by_cases hr : IsRemCorner η r
      · rw [ite_eq_left hr, hookWalkProb_of_le h, ite_eq_right]
        simp only [Prod.mk.injEq]
        rintro ⟨rfl, -⟩
        exact hne rfl
      · rw [ite_eq_right hr]
  intro N
  induction N with
  | zero =>
    intro i j hN hc
    exact base i j hc (hookLength_le_one_of_sum_le (by omega) (by omega))
  | succ N ih =>
    intro i j hN hc
    by_cases h : hookLength η i j ≤ 1
    · exact base i j hc h
    · have hrow : ∀ j' ∈ Finset.Ioo j (η.getD i 0),
          ∑ r ∈ Finset.range η.length,
            (if IsRemCorner η r then hookWalkProb η (r, η.getD r 0 - 1) (i, j') else 0)
              = 1 := by
        intro j' hj'
        rw [Finset.mem_Ioo] at hj'
        have hle : η.getD i 0 ≤ η.sum := getD_le_sum _ _
        exact ih i j' (by omega) hj'.2
      have hcol : ∀ i' ∈ Finset.Ioo i ((conjPart η).getD j 0),
          ∑ r ∈ Finset.range η.length,
            (if IsRemCorner η r then hookWalkProb η (r, η.getD r 0 - 1) (i', j) else 0)
              = 1 := by
        intro i' hi'
        rw [Finset.mem_Ioo] at hi'
        have hle : (conjPart η).getD j 0 ≤ η.sum := by
          simpa using getD_le_sum (conjPart η) j
        exact ih i' j (by omega) (lt_getD_of_lt_getD_conjPart hη hi'.2)
      have hcard := card_hook_moves hη hc
      have hpos : (1 : ℚ) ≤ (hookLength η i j : ℚ) - 1 := by
        have : (2 : ℕ) ≤ hookLength η i j := by omega
        have : (2 : ℚ) ≤ (hookLength η i j : ℚ) := by exact_mod_cast this
        linarith
      have hne : ((hookLength η i j : ℚ) - 1) ≠ 0 := by linarith
      have hexp : ∀ r : ℕ, (if IsRemCorner η r then
            hookWalkProb η (r, η.getD r 0 - 1) (i, j) else 0)
          = ((∑ j' ∈ Finset.Ioo j (η.getD i 0),
                (if IsRemCorner η r then hookWalkProb η (r, η.getD r 0 - 1) (i, j')
                  else 0)) +
             (∑ i' ∈ Finset.Ioo i ((conjPart η).getD j 0),
                (if IsRemCorner η r then hookWalkProb η (r, η.getD r 0 - 1) (i', j)
                  else 0))) / ((hookLength η i j : ℚ) - 1) := by
        intro r
        by_cases hr : IsRemCorner η r
        · simp only [ite_eq_left hr]
          exact hookWalkProb_of_lt (x := (i, j)) (Nat.lt_of_not_le h)
        · simp [ite_eq_right hr]
      rw [Finset.sum_congr rfl fun r _ => hexp r, ← Finset.sum_div, Finset.sum_add_distrib,
        Finset.sum_comm (s := Finset.range η.length) (t := Finset.Ioo j (η.getD i 0)),
        Finset.sum_comm (s := Finset.range η.length)
          (t := Finset.Ioo i ((conjPart η).getD j 0)),
        Finset.sum_congr rfl fun j' hj' => hrow j' hj',
        Finset.sum_congr rfl fun i' hi' => hcol i' hi']
      rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one, mul_one]
      rw [div_eq_one_iff_eq hne]
      have : ((Finset.Ioo j (η.getD i 0)).card : ℚ) +
          ((Finset.Ioo i ((conjPart η).getD j 0)).card : ℚ)
          = ((hookLength η i j - 1 : ℕ) : ℚ) := by
        rw [← hcard]
        push_cast
        ring
      rw [this]
      have h1 : (1 : ℕ) ≤ hookLength η i j := one_le_hookLength hη hc
      have := Nat.cast_sub (R := ℚ) h1
      simpa using this

/-- **The hook walk ends at a corner**: starting from any box of the diagram, the
probabilities of ending at the various removable corners add up to one. -/
theorem sum_hookWalkProb_corners (hη : IsPart η) {i j : ℕ} (hc : j < η.getD i 0) :
    ∑ r ∈ Finset.range η.length,
        (if IsRemCorner η r then hookWalkProb η (r, η.getD r 0 - 1) (i, j) else 0) = 1 :=
  sum_hookWalkProb_corners_aux hη _ i j le_rfl hc

/-! ### The Greene–Nijenhuis–Wilf formula -/

/-- The factor attached to the row `i` in the Greene–Nijenhuis–Wilf formula for the corner at
the end of the row `al`: the inverse of the number of boxes strictly inside the hook of the
box `(i, be)`, where `be` is the column of the corner (and `1` for the row of the corner
itself). -/
def gnwRow (η : List ℕ) (al i : ℕ) : ℚ :=
  if i = al then 1 else ((hookLength η i (η.getD al 0 - 1) : ℚ) - 1)⁻¹

/-- The factor attached to the column `j` in the Greene–Nijenhuis–Wilf formula for the corner
at the end of the row `al`: the inverse of the number of boxes strictly inside the hook of
the box `(al, j)` (and `1` for the column of the corner itself). -/
def gnwCol (η : List ℕ) (al j : ℕ) : ℚ :=
  if j = η.getD al 0 - 1 then 1 else ((hookLength η al j : ℚ) - 1)⁻¹

@[simp] lemma gnwRow_self (η : List ℕ) (al : ℕ) : gnwRow η al al = 1 := by
  simp [gnwRow]

lemma gnwCol_self (η : List ℕ) (al : ℕ) : gnwCol η al (η.getD al 0 - 1) = 1 := by
  simp [gnwCol]

variable {al : ℕ}

/-- The column of a removable corner is the last column of its row. -/
lemma getD_corner (hal : IsRemCorner η al) : η.getD al 0 = (η.getD al 0 - 1) + 1 := by
  simp only [IsRemCorner] at hal
  omega

/-- The conjugate of the diagram at the column of a removable corner. -/
lemma getD_conjPart_corner (hη : IsPart η) (hal : IsRemCorner η al) :
    (conjPart η).getD (η.getD al 0 - 1) 0 = al + 1 := by
  have h1 : η.getD al 0 - 1 < η.getD al 0 := by
    simp only [IsRemCorner] at hal; omega
  have h2 : al < (conjPart η).getD (η.getD al 0 - 1) 0 := lt_getD_conjPart hη h1
  have h3 : η.getD (al + 1) 0 ≤ η.getD al 0 - 1 := by
    simp only [IsRemCorner] at hal; omega
  have h4 := (getD_le_conjPart_iff hη (al + 1) (η.getD al 0 - 1)).1 h3
  omega

/-- Every box in a row above a removable corner and in the column of that corner is a box of
the diagram. -/
lemma corner_lt_getD (hη : IsPart η) (hal : IsRemCorner η al) {a : ℕ} (ha : a ≤ al) :
    η.getD al 0 - 1 < η.getD a 0 := by
  have h1 : η.getD al 0 ≤ η.getD a 0 := hη.getD_antitone ha
  simp only [IsRemCorner] at hal
  omega

/-- The hook lengths appearing in the Greene–Nijenhuis–Wilf recursion: the hook of a box
`(a, b)` above and to the left of a corner `(al, be)` has one box less than the union of the
hooks of `(a, be)` and `(al, b)`. -/
lemma hookLength_add_hookLength (hη : IsPart η) (hal : IsRemCorner η al) {a b : ℕ}
    (ha : a ≤ al) (hb : b ≤ η.getD al 0 - 1) :
    hookLength η a (η.getD al 0 - 1) + hookLength η al b = hookLength η a b + 1 := by
  have hbe : η.getD al 0 - 1 < η.getD a 0 := corner_lt_getD hη hal ha
  have hcell : b < η.getD a 0 := by omega
  have hbal : b < η.getD al 0 := by
    simp only [IsRemCorner] at hal; omega
  have h1 := hookLength_add_one hη hbe
  have h2 := hookLength_add_one hη hbal
  have h3 := hookLength_add_one hη hcell
  have h4 := getD_conjPart_corner hη hal
  have h5 : (conjPart η).getD (η.getD al 0 - 1) 0 ≤ (conjPart η).getD b 0 :=
    (isPart_conjPart hη).getD_antitone hb
  omega

/-- Above a removable corner, in the column of the corner, the hook has more than one box. -/
lemma one_lt_hookLength_col (hη : IsPart η) (hal : IsRemCorner η al) {a : ℕ}
    (ha : a < al) : 1 < hookLength η a (η.getD al 0 - 1) := by
  have hbe : η.getD al 0 - 1 < η.getD a 0 := corner_lt_getD hη hal (le_of_lt ha)
  have h1 := hookLength_add_one hη hbe
  have h4 := getD_conjPart_corner hη hal
  omega

/-- To the left of a removable corner, in the row of the corner, the hook has more than one
box. -/
lemma one_lt_hookLength_row (hη : IsPart η) (hal : IsRemCorner η al) {b : ℕ}
    (hb : b < η.getD al 0 - 1) : 1 < hookLength η al b := by
  have hbal : b < η.getD al 0 := by
    simp only [IsRemCorner] at hal; omega
  have h2 := hookLength_add_one hη hbal
  have h5 : al < (conjPart η).getD b 0 := lt_getD_conjPart hη hbal
  omega

private lemma hookWalkProb_corner_aux (hη : IsPart η) (hal : IsRemCorner η al) (be : ℕ)
    (hbe : η.getD al 0 = be + 1) :
    ∀ (N a b : ℕ), (al - a) + (be - b) ≤ N → a ≤ al → b ≤ be →
      hookWalkProb η (al, be) (a, b)
        = gnwRow η al a * gnwCol η al b *
          (∏ i ∈ Finset.Ioo a al, (1 + gnwRow η al i)) *
          (∏ j ∈ Finset.Ioo b be, (1 + gnwCol η al j)) := by
  have hbeval : η.getD al 0 - 1 = be := by omega
  have hrowval : ∀ i : ℕ, i ≠ al → gnwRow η al i = ((hookLength η i be : ℚ) - 1)⁻¹ := by
    intro i hi
    rw [gnwRow, ite_eq_right hi, hbeval]
  have hcolval : ∀ j : ℕ, j ≠ be → gnwCol η al j = ((hookLength η al j : ℚ) - 1)⁻¹ := by
    intro j hj
    rw [gnwCol, ite_eq_right (by rw [hbeval]; exact hj)]
  have hcolone : gnwCol η al be = 1 := by rw [gnwCol, ite_eq_left hbeval.symm]
  have hconjbe : (conjPart η).getD be 0 = al + 1 := by
    have := getD_conjPart_corner hη hal
    rwa [hbeval] at this
  have hcellrow : ∀ a : ℕ, a ≤ al → be < η.getD a 0 := by
    intro a ha
    have := corner_lt_getD hη hal ha
    rwa [hbeval] at this
  -- the base case: the walk has stopped
  have base : ∀ a b : ℕ, a ≤ al → b ≤ be → hookLength η a b ≤ 1 →
      hookWalkProb η (al, be) (a, b)
        = gnwRow η al a * gnwCol η al b *
          (∏ i ∈ Finset.Ioo a al, (1 + gnwRow η al i)) *
          (∏ j ∈ Finset.Ioo b be, (1 + gnwCol η al j)) := by
    intro a b ha hb h
    have hbea : be < η.getD a 0 := hcellrow a ha
    have hcell : b < η.getD a 0 := by omega
    have h1 : hookLength η a b = 1 := le_antisymm h (one_le_hookLength hη hcell)
    have h2 := hookLength_add_one hη hcell
    have h3 : a < (conjPart η).getD b 0 := lt_getD_conjPart hη hcell
    have hbb : b = be := by omega
    subst hbb
    have h5 : a = al := by omega
    subst h5
    rw [hookWalkProb_of_le h, ite_eq_left rfl, gnwRow_self, hcolone]
    simp
  intro N
  induction N with
  | zero =>
    intro a b hN ha hb
    have haa : a = al := by omega
    have hbb : b = be := by omega
    subst haa; subst hbb
    refine base a b le_rfl le_rfl ?_
    have hcell : b < η.getD a 0 := hcellrow a le_rfl
    have h2 := hookLength_add_one hη hcell
    omega
  | succ N ih =>
    intro a b hN ha hb
    by_cases hstop : hookLength η a b ≤ 1
    · exact base a b ha hb hstop
    have hbea : be < η.getD a 0 := hcellrow a ha
    have hcell : b < η.getD a 0 := by omega
    have hconj : al < (conjPart η).getD b 0 := by
      have h5 : (conjPart η).getD be 0 ≤ (conjPart η).getD b 0 :=
        (isPart_conjPart hη).getD_antitone hb
      omega
    -- the sum over the boxes to the right of `(a, b)`
    have hrow : ∑ j ∈ Finset.Ioo b (η.getD a 0), hookWalkProb η (al, be) (a, j)
        = gnwRow η al a * (∏ i ∈ Finset.Ioo a al, (1 + gnwRow η al i)) *
            ∑ j ∈ Finset.Ioc b be, gnwCol η al j *
              ∏ j' ∈ Finset.Ioo j be, (1 + gnwCol η al j') := by
      rw [← Finset.sum_subset (s₁ := Finset.Ioc b be) (by
        intro j hj
        rw [Finset.mem_Ioc] at hj
        rw [Finset.mem_Ioo]
        omega)]
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_Ioc] at hj
        rw [ih a j (by omega) ha (by omega)]
        ring
      · intro j hj hj'
        rw [Finset.mem_Ioo] at hj
        rw [Finset.mem_Ioc] at hj'
        exact hookWalkProb_eq_zero_of_not_le (by simp only; omega)
    -- the sum over the boxes below `(a, b)`
    have hcol : ∑ i ∈ Finset.Ioo a ((conjPart η).getD b 0), hookWalkProb η (al, be) (i, b)
        = gnwCol η al b * (∏ j ∈ Finset.Ioo b be, (1 + gnwCol η al j)) *
            ∑ i ∈ Finset.Ioc a al, gnwRow η al i *
              ∏ i' ∈ Finset.Ioo i al, (1 + gnwRow η al i') := by
      rw [← Finset.sum_subset (s₁ := Finset.Ioc a al) (by
        intro i hi
        rw [Finset.mem_Ioc] at hi
        rw [Finset.mem_Ioo]
        omega)]
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.mem_Ioc] at hi
        rw [ih i b (by omega) hi.2 hb]
        ring
      · intro i hi hi'
        rw [Finset.mem_Ioo] at hi
        rw [Finset.mem_Ioc] at hi'
        exact hookWalkProb_eq_zero_of_not_le (by simp only; omega)
    -- the two telescoping sums
    have htelrow : ∑ j ∈ Finset.Ioc b be, gnwCol η al j *
          ∏ j' ∈ Finset.Ioo j be, (1 + gnwCol η al j')
        = if b = be then 0 else ∏ j ∈ Finset.Ioo b be, (1 + gnwCol η al j) := by
      rcases eq_or_lt_of_le hb with heq | hlt
      · rw [ite_eq_left heq, heq]
        simp
      · rw [ite_eq_right (by omega),
          show Finset.Ioc b be = Finset.Icc (b + 1) be by
            ext j; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega,
          sum_Icc_mul_prod_Ioo (gnwCol η al) be (be - (b + 1)) (b + 1) (by omega),
          show Finset.Ico (b + 1) be = Finset.Ioo b be from rfl, hcolone]
        ring
    have htelcol : ∑ i ∈ Finset.Ioc a al, gnwRow η al i *
          ∏ i' ∈ Finset.Ioo i al, (1 + gnwRow η al i')
        = if a = al then 0 else ∏ i ∈ Finset.Ioo a al, (1 + gnwRow η al i) := by
      rcases eq_or_lt_of_le ha with heq | hlt
      · rw [ite_eq_left heq, heq]
        simp
      · rw [ite_eq_right (by omega),
          show Finset.Ioc a al = Finset.Icc (a + 1) al by
            ext i; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega,
          sum_Icc_mul_prod_Ioo (gnwRow η al) al (al - (a + 1)) (a + 1) (by omega),
          show Finset.Ico (a + 1) al = Finset.Ioo a al from rfl, gnwRow_self]
        ring
    have hne : ((hookLength η a b : ℚ) - 1) ≠ 0 := by
      have h2 : (2 : ℕ) ≤ hookLength η a b := by omega
      have : (2 : ℚ) ≤ (hookLength η a b : ℚ) := by exact_mod_cast h2
      intro hcon
      linarith
    rw [hookWalkProb_of_lt (x := (a, b)) (Nat.lt_of_not_le hstop)]
    simp only
    rw [hrow, hcol, htelrow, htelcol, div_eq_iff hne]
    -- the three remaining cases
    rcases eq_or_lt_of_le ha with heqa | halt
    · -- the box is in the row of the corner
      have hga : η.getD a 0 = be + 1 := by rw [heqa]; exact hbe
      have hblt : b < be := by
        rcases eq_or_lt_of_le hb with heqb | h
        · exfalso
          have h1 := hookLength_add_one hη hcell
          have h2 : (conjPart η).getD b 0 = al + 1 := by rw [heqb]; exact hconjbe
          omega
        · exact h
      rw [ite_eq_right (by omega : ¬ b = be), ite_eq_left heqa, heqa, gnwRow_self,
        hcolval b (by omega)]
      have hne' : ((hookLength η al b : ℚ) - 1) ≠ 0 := by rwa [heqa] at hne
      simp only [Finset.Ioo_self, Finset.prod_empty]
      field_simp
      ring
    · rcases eq_or_lt_of_le hb with heqb | hblt
      · -- the box is in the column of the corner
        rw [ite_eq_left heqb, ite_eq_right (by omega : ¬ a = al), heqb, hcolone,
          hrowval a (by omega)]
        have hne' : ((hookLength η a be : ℚ) - 1) ≠ 0 := by rwa [heqb] at hne
        simp only [Finset.Ioo_self, Finset.prod_empty]
        field_simp
        ring
      · -- the generic case
        rw [ite_eq_right (by omega), ite_eq_right (by omega), hrowval a (by omega),
          hcolval b (by omega)]
        have hkey : hookLength η a be + hookLength η al b = hookLength η a b + 1 := by
          have := hookLength_add_hookLength hη hal (b := b) ha (by omega)
          rwa [hbeval] at this
        have hr2 : (2 : ℕ) ≤ hookLength η a be := by
          have := one_lt_hookLength_col hη hal halt
          rw [hbeval] at this
          omega
        have hc2 : (2 : ℕ) ≤ hookLength η al b := by
          have := one_lt_hookLength_row hη hal (b := b) (by omega)
          omega
        have hrQ : (2 : ℚ) ≤ (hookLength η a be : ℚ) := by exact_mod_cast hr2
        have hcQ : (2 : ℚ) ≤ (hookLength η al b : ℚ) := by exact_mod_cast hc2
        have hsum : (hookLength η a be : ℚ) + (hookLength η al b : ℚ)
            = (hookLength η a b : ℚ) + 1 := by exact_mod_cast hkey
        have h1 : ((hookLength η a be : ℚ) - 1) ≠ 0 := by intro hcon; linarith
        have h2 : ((hookLength η al b : ℚ) - 1) ≠ 0 := by intro hcon; linarith
        field_simp
        have hlin : (hookLength η al b : ℚ) - 1 + ((hookLength η a be : ℚ) - 1)
            = (hookLength η a b : ℚ) - 1 := by linarith
        rw [hlin]

/-- **The Greene–Nijenhuis–Wilf formula**: the probability that the hook walk started at a
box `(a, b)` weakly above and to the left of the corner `(al, be)` ends at that corner. -/
theorem hookWalkProb_corner (hη : IsPart η) (hal : IsRemCorner η al) {a b : ℕ}
    (ha : a ≤ al) (hb : b ≤ η.getD al 0 - 1) :
    hookWalkProb η (al, η.getD al 0 - 1) (a, b)
      = gnwRow η al a * gnwCol η al b *
        (∏ i ∈ Finset.Ioo a al, (1 + gnwRow η al i)) *
        (∏ j ∈ Finset.Ioo b (η.getD al 0 - 1), (1 + gnwCol η al j)) :=
  hookWalkProb_corner_aux hη hal _ (getD_corner hal) _ a b le_rfl ha hb

end Young
