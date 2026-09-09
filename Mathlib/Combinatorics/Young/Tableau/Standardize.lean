/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.Plactic.Monoid

/-!
# Standardizing a tableau

A Lean 4 port of the standardization of tableaux of `theories/Combi/stdtab.v` and
`theories/LRrule/stdplact.v` of [Coq-Combi](https://github.com/math-comp/Coq-Combi).

Standardizing the reading word of a tableau `t` and cutting the result along the rows of
`t` produces a *standard* tableau of the same shape as `t`, whose reading word is the
standardization of the reading word of `t`.  Consequently the insertion tableau of the
standardization of the reading word of a tableau has the same shape as the tableau.

## Main definitions

* `List.reshapeLike t v` : cut the word `v` into rows following the shape of `t`.
* `List.stdTabOf t` : the standardization of the tableau `t`.

## Main results

* `List.isTableau_reshapeLike` : cutting a word which has the same pattern of relative
  order as the reading word of a tableau produces a tableau.
* `List.isStdTab_stdTabOf`, `List.shape_stdTabOf`, `List.toWord_stdTabOf` : the
  standardization of a tableau is a standard tableau of the same shape, whose reading word
  is the standardization of the reading word.
* `List.shape_RS_std_toWord` : the insertion tableau of the standardized reading word of
  a tableau has the shape of the tableau.
-/

@[expose] public section

namespace List

open List

/-! ### Cutting a word along the rows of a tableau -/

/-- Cut the word `v` into rows following the shape of the tableau `t`; the last letters of
`v` form the first row, as in the reading word `List.toWord`. -/
def reshapeLike {T α : Type*} : List (List T) → List α → List (List α)
  | [], _ => []
  | t0 :: t, v => v.drop (v.length - t0.length) :: reshapeLike t (v.take (v.length - t0.length))

variable {T α : Type*}

@[simp] lemma reshapeLike_nil (v : List α) : reshapeLike ([] : List (List T)) v = [] := rfl

lemma reshapeLike_cons (t0 : List T) (t : List (List T)) (v : List α) :
    reshapeLike (t0 :: t) v =
      v.drop (v.length - t0.length) :: reshapeLike t (v.take (v.length - t0.length)) := rfl

lemma sizeTab_cons (t0 : List T) (t : List (List T)) :
    sizeTab (t0 :: t) = t0.length + sizeTab t := by
  simp [sizeTab]

lemma shape_reshapeLike : ∀ (t : List (List T)) (v : List α), v.length = sizeTab t →
    shape (reshapeLike t v) = shape t := by
  intro t
  induction t with
  | nil => intro v _; simp
  | cons t0 t ih =>
    intro v hv
    rw [sizeTab_cons] at hv
    have hk : v.length - t0.length = sizeTab t := by omega
    have hvt : (v.take (v.length - t0.length)).length = sizeTab t := by
      simp only [List.length_take]; omega
    rw [reshapeLike_cons, shape_cons, shape_cons, ih _ hvt, List.length_drop]
    congr 1
    omega

lemma toWord_reshapeLike : ∀ (t : List (List T)) (v : List α), v.length = sizeTab t →
    toWord (reshapeLike t v) = v := by
  intro t
  induction t with
  | nil =>
    intro v hv
    simp only [sizeTab, shape_nil, List.sum_nil] at hv
    rw [reshapeLike_nil, toWord_nil, List.eq_nil_of_length_eq_zero hv]
  | cons t0 t ih =>
    intro v hv
    rw [sizeTab_cons] at hv
    have hk : v.length - t0.length = sizeTab t := by omega
    have hvt : (v.take (v.length - t0.length)).length = sizeTab t := by
      simp only [List.length_take]; omega
    rw [reshapeLike_cons, toWord_cons, ih _ hvt, hk, List.take_append_drop]

lemma length_head_reshapeLike (t0 : List T) (t : List (List T)) (v : List α) :
    ((reshapeLike (t0 :: t) v).headD []).length = v.length - (v.length - t0.length) := by
  rw [reshapeLike_cons]
  simp

/-! ### Transferring the tableau structure -/

variable [LinearOrder T] [LinearOrder α]

/-- If the word `v` has the same pattern of relative order as the reading word of the
tableau `t`, then cutting it along the rows of `t` produces a tableau. -/
theorem isTableau_reshapeLike : ∀ (t : List (List T)) (v : List α), IsTableau t →
    ∀ (hlen : v.length = (toWord t).length),
    (∀ i j, (hi : i < (toWord t).length) → (hj : j < (toWord t).length) → i < j →
      (toWord t)[i] ≤ (toWord t)[j] → v[i]'(by omega) < v[j]'(by omega)) →
    (∀ i j, (hi : i < (toWord t).length) → (hj : j < (toWord t).length) →
      (toWord t)[i] < (toWord t)[j] → v[i]'(by omega) < v[j]'(by omega)) →
    IsTableau (reshapeLike t v) := by
  intro t
  induction t with
  | nil => intro v _ _ _ _; simp
  | cons t0 t ih =>
    intro v ht hlen hle hlt
    obtain ⟨hne, hrow, hdom, htab⟩ := ht
    have hlent : (toWord (t0 :: t)).length = (toWord t).length + t0.length := by
      rw [toWord_cons, List.length_append]
    have hvk : v.length - t0.length = (toWord t).length := by omega
    have hn0 : 0 < t0.length := List.length_pos_iff.2 hne
    have hgetw : ∀ i (hi : i < (toWord t).length),
        (toWord (t0 :: t))[i]'(by omega) = (toWord t)[i] := by
      intro i hi
      simp only [toWord_cons]
      exact List.getElem_append_left hi
    have hgetw0 : ∀ c (hc : c < t0.length),
        (toWord (t0 :: t))[(toWord t).length + c]'(by omega) = t0[c] := by
      intro c hc
      simp only [toWord_cons]
      rw [List.getElem_append_right (by omega)]
      simp
    rw [reshapeLike_cons, hvk]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hl : (v.drop (toWord t).length).length = t0.length := by
        simp only [List.length_drop]; omega
      intro hcon
      rw [hcon] at hl
      simp only [List.length_nil] at hl
      omega
    · rw [IsRow, List.isChain_iff_pairwise, List.pairwise_iff_getElem]
      intro c c' hc hc' hcc
      simp only [List.length_drop] at hc hc'
      have hc0' : c' < t0.length := by omega
      have hstep : (toWord (t0 :: t))[(toWord t).length + c]'(by omega)
          ≤ (toWord (t0 :: t))[(toWord t).length + c']'(by omega) := by
        rw [hgetw0 c (by omega), hgetw0 c' hc0']
        exact hrow.getElem_le (le_of_lt hcc) hc0'
      have key := hle ((toWord t).length + c) ((toWord t).length + c')
        (by omega) (by omega) (by omega) hstep
      simpa [List.getElem_drop] using le_of_lt key
    · cases t with
      | nil => simp
      | cons t1 t' =>
        have hdom1 : Dominate t1 t0 := hdom
        have hlen1 : (toWord (t1 :: t')).length = (toWord t').length + t1.length := by
          rw [toWord_cons, List.length_append]
        have hvtake : (v.take (toWord (t1 :: t')).length).length = (toWord (t1 :: t')).length := by
          simp only [List.length_take]; omega
        have hhead : (reshapeLike (t1 :: t') (v.take (toWord (t1 :: t')).length)).headD []
            = (v.take (toWord (t1 :: t')).length).drop ((toWord t').length) := by
          rw [reshapeLike_cons]
          simp only [List.headD_cons, hvtake]
          congr 1
          omega
        rw [hhead]
        refine dominate_of_getElem ?_ ?_
        · simp only [List.length_drop, List.length_take]
          have := hdom1.length_le
          omega
        · intro c hc
          simp only [List.length_drop, List.length_take] at hc
          have hc1 : c < t1.length := by omega
          have hc0 : c < t0.length := lt_of_lt_of_le hc1 hdom1.length_le
          have hgetw1 : (toWord (t0 :: t1 :: t'))[(toWord t').length + c]'(by omega) = t1[c] := by
            rw [hgetw ((toWord t').length + c) (by omega)]
            simp only [toWord_cons]
            rw [List.getElem_append_right (by omega)]
            simp
          have hstep : (toWord (t0 :: t1 :: t'))[(toWord (t1 :: t')).length + c]'(by omega)
              < (toWord (t0 :: t1 :: t'))[(toWord t').length + c]'(by omega) := by
            rw [hgetw0 c hc0, hgetw1]
            exact hdom1.getElem_lt c hc1
          have key := hlt ((toWord (t1 :: t')).length + c) ((toWord t').length + c)
            (by omega) (by omega) hstep
          simpa [List.getElem_drop, List.getElem_take] using key
    · refine ih (v.take (toWord t).length) htab (by simp only [List.length_take]; omega) ?_ ?_
      · intro i j hi hj hij hij'
        have hstep : (toWord (t0 :: t))[i]'(by omega) ≤ (toWord (t0 :: t))[j]'(by omega) := by
          rw [hgetw i hi, hgetw j hj]; exact hij'
        have key := hle i j (by omega) (by omega) hij hstep
        simpa [List.getElem_take] using key
      · intro i j hi hj hij'
        have hstep : (toWord (t0 :: t))[i]'(by omega) < (toWord (t0 :: t))[j]'(by omega) := by
          rw [hgetw i hi, hgetw j hj]; exact hij'
        have key := hlt i j (by omega) (by omega) hstep
        simpa [List.getElem_take] using key

/-! ### The standardization of a tableau -/

/-- The standardization of a tableau: standardize the reading word and cut it along the
rows of the tableau. -/
def stdTabOf (t : List (List T)) : List (List ℕ) := reshapeLike t (std (toWord t))

@[simp] lemma shape_stdTabOf (t : List (List T)) : shape (stdTabOf t) = shape t :=
  shape_reshapeLike t _ (by rw [length_std, length_toWord])

@[simp] lemma toWord_stdTabOf (t : List (List T)) : toWord (stdTabOf t) = std (toWord t) :=
  toWord_reshapeLike t _ (by rw [length_std, length_toWord])

lemma isTableau_stdTabOf {t : List (List T)} (ht : IsTableau t) : IsTableau (stdTabOf t) := by
  refine isTableau_reshapeLike t _ ht (by rw [length_std]) ?_ ?_
  · intro i j hi hj hij h
    refine (getElem_std_lt_getElem_std_iff (toWord t) hi hj).2 ?_
    rcases lt_or_eq_of_le h with h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨h', hij⟩
  · intro i j hi hj h
    exact (getElem_std_lt_getElem_std_iff (toWord t) hi hj).2 (Or.inl h)

/-- The standardization of a tableau is a standard tableau. -/
theorem isStdTab_stdTabOf {t : List (List T)} (ht : IsTableau t) : IsStdTab (stdTabOf t) :=
  ⟨isTableau_stdTabOf ht, by rw [toWord_stdTabOf]; exact std_isStd _⟩

/-- The insertion tableau of the standardized reading word of a tableau has the shape of
the tableau. -/
theorem shape_RS_std_toWord {t : List (List T)} (ht : IsTableau t) :
    shape (RS (std (toWord t))) = shape t := by
  rw [← toWord_stdTabOf t, RS_toWord (isTableau_stdTabOf ht), shape_stdTabOf]

end List
