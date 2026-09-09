/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Combinatorics.Enumerative.DyckWord.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Prod

/-!
# The cycle lemma and the enumeration of Dyck words

A Lean 4 port of the second half of `theories/Combi/Dyckword.v` from
[Coq-Combi](https://github.com/math-comp/Coq-Combi), namely the *rotation trick*
counting Dyck words.

Let `w` be a word of height `-1`, that is, with one more `D` than `U`s.  Among the
rotations of `w` there is exactly one which is a Dyck word followed by a final `D`
(Coq `rot_is_Dyck` together with the injectivity statements of the section
`DyckWordRotationBijection`).  The rotation index realizing this is the first
position at which the prefix heights of `w` reach their minimum.

Consequences: the words of length `2 * n + 1` with `n` letters `U` are in bijection
with the pairs made of a Dyck word of length `2 * n` and of a rotation index, which
gives the Catalan formula `(2 * n + 1) * catalan n = (2 * n + 1).choose n`
(Coq `card_Dyck_hsz`), as well as the fact that the `(2 * n).choose n` balanced words
of length `2 * n` are `n + 1` times as many as the Dyck words (Coq
`card_bal_Dyck_hsz`).

## Main definitions

* `List.prefHeight w i` : the height of the prefix of length `i` of `w`.
* `List.IsFirstMin w k` : `k` is the first index at which the prefix heights of `w`
  attain their minimum; `List.firstMinIdx w` is that index (Coq `pfminh`).

## Main results

* `List.isDyckWord_dropLast_rotate_iff` : for a word of height `-1`, rotating by `k`
  gives a Dyck word followed by a final `D` exactly when `k` is the first minimum of
  the prefix heights (Coq `rot_is_Dyck`).
* `List.existsUnique_isDyckWord_dropLast_rotate` : the **cycle lemma**: such a `k` is
  unique.
* `List.cycleEquiv` : the resulting bijection between the words of length `2 * n + 1`
  with `n` letters `U` and the pairs (Dyck word of length `2 * n`, rotation index).
* `List.card_words_count_eq` : there are `m.choose k` words of length `m` with `k`
  letters `U` (Coq `card_bal_hsz`).
* `List.succ_two_mul_catalan_eq_choose` : `(2 * n + 1) * catalan n = (2 * n + 1).choose n`
  (Coq `card_Dyck_hsz`).
* `List.card_balanced_eq_succ_mul_catalan` : the balanced words of length `2 * n` are
  `n + 1` times as many as the Dyck words of length `2 * n` (Coq `card_bal_Dyck_hsz`).
-/

@[expose] public section

namespace List

open List DyckStep Finset

/-! ### Prefix heights -/

/-- The height of the prefix of length `i` of the word `w`. -/
def prefHeight (w : List DyckStep) (i : ℕ) : ℤ := dyckHeight (w.take i)

@[simp] lemma prefHeight_zero (w : List DyckStep) : prefHeight w 0 = 0 := by simp [prefHeight]

lemma prefHeight_of_length_le {w : List DyckStep} {i : ℕ} (h : w.length ≤ i) :
    prefHeight w i = dyckHeight w := by
  rw [prefHeight, take_of_length_le h]

@[simp] lemma prefHeight_length (w : List DyckStep) : prefHeight w w.length = dyckHeight w :=
  prefHeight_of_length_le le_rfl

lemma prefHeight_succ (w : List DyckStep) (i : ℕ) :
    prefHeight w (i + 1) = prefHeight w i + dyckHeight w[i]?.toList := by
  rw [prefHeight, prefHeight, List.take_add_one, dyckHeight_append]

/-- Two consecutive prefix heights differ by at most one. -/
lemma prefHeight_le_prefHeight_succ_add_one (w : List DyckStep) (i : ℕ) :
    prefHeight w i ≤ prefHeight w (i + 1) + 1 := by
  rw [prefHeight_succ]
  rcases h : w[i]? with _ | s
  · simp
  · cases s
    · simp
      omega
    · simp

/-! ### The first minimum of the prefix heights -/

/-- `k` is the first index at which the prefix heights of `w` attain their minimum
(Coq `pfminh`). -/
def IsFirstMin (w : List DyckStep) (k : ℕ) : Prop :=
  (∀ j ≤ w.length, prefHeight w k ≤ prefHeight w j) ∧ ∀ j < k, prefHeight w k < prefHeight w j

lemma IsFirstMin.le_length {w : List DyckStep} {k : ℕ} (h : IsFirstMin w k) : k ≤ w.length := by
  by_contra hk
  push Not at hk
  have h1 := h.2 w.length hk
  rw [prefHeight_of_length_le hk.le, prefHeight_length] at h1
  exact absurd h1 (lt_irrefl _)

lemma IsFirstMin.unique {w : List DyckStep} {k k' : ℕ} (h : IsFirstMin w k)
    (h' : IsFirstMin w k') : k = k' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd (h.1 k' h'.le_length) (not_le.2 (h'.2 k hlt))
  · exact absurd (h'.1 k h.le_length) (not_le.2 (h.2 k' hlt))

lemma exists_isFirstMin (w : List DyckStep) : ∃ k, IsFirstMin w k := by
  classical
  have hex : ∃ k, ∀ j ≤ w.length, prefHeight w k ≤ prefHeight w j := by
    obtain ⟨x, -, hmin⟩ :=
      Finset.exists_min_image (Finset.range (w.length + 1)) (prefHeight w) ⟨0, by simp⟩
    exact ⟨x, fun j hj ↦ hmin j (by simp; omega)⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, fun j hj ↦ ?_⟩
  have hnot := Nat.find_min hex hj
  push Not at hnot
  obtain ⟨i, hi, hlt⟩ := hnot
  exact lt_of_le_of_lt (Nat.find_spec hex i hi) hlt

open Classical in
/-- The first index at which the prefix heights of `w` attain their minimum (Coq `pfminh`). -/
noncomputable def firstMinIdx (w : List DyckStep) : ℕ := (exists_isFirstMin w).choose

lemma isFirstMin_firstMinIdx (w : List DyckStep) : IsFirstMin w (firstMinIdx w) :=
  (exists_isFirstMin w).choose_spec

lemma firstMinIdx_eq_of_isFirstMin {w : List DyckStep} {k : ℕ} (h : IsFirstMin w k) :
    firstMinIdx w = k :=
  (isFirstMin_firstMinIdx w).unique h

/-! ### Prefix heights of a rotation -/

lemma dyckHeight_take_rotate_of_le {w : List DyckStep} {k i : ℕ} (hk : k ≤ w.length)
    (hi : i ≤ w.length - k) :
    dyckHeight ((w.rotate k).take i) = prefHeight w (k + i) - prefHeight w k := by
  rw [rotate_eq_drop_append_take hk, take_append]
  have h1 : i - (w.drop k).length = 0 := by simp; omega
  rw [h1, take_zero, append_nil, take_drop, dyckHeight_drop, take_take,
    Nat.min_eq_left (by omega)]
  rfl

lemma dyckHeight_take_rotate_of_ge {w : List DyckStep} {k i : ℕ} (hk : k ≤ w.length)
    (h1 : w.length - k ≤ i) (h2 : i ≤ w.length) :
    dyckHeight ((w.rotate k).take i) =
      dyckHeight w - prefHeight w k + prefHeight w (i - (w.length - k)) := by
  rw [rotate_eq_drop_append_take hk, take_append, take_of_length_le (by simp; omega),
    dyckHeight_append, dyckHeight_drop, length_drop, take_take, Nat.min_eq_left (by omega)]
  rfl

/-! ### The cycle lemma -/

/-- For a word of height `-1`, the rotations that give a Dyck word followed by a final `D`
are exactly the rotations at the first minimum of the prefix heights (Coq `rot_is_Dyck`). -/
theorem isDyckWord_dropLast_rotate_iff {w : List DyckStep} (hw : dyckHeight w = -1) {k : ℕ}
    (hk1 : 1 ≤ k) (hk2 : k ≤ w.length) :
    IsDyckWord ((w.rotate k).dropLast) ↔ IsFirstMin w k := by
  have hlen : (w.rotate k).length = w.length := length_rotate w k
  have hm : 1 ≤ w.length := le_trans hk1 hk2
  have hdrop : (w.rotate k).dropLast = (w.rotate k).take (w.length - 1) := by
    rw [dropLast_eq_take, hlen]
  have hdroplen : (w.rotate k).dropLast.length = w.length - 1 := by
    rw [length_dropLast, hlen]
  have htake : ∀ i ≤ w.length - 1,
      ((w.rotate k).dropLast).take i = (w.rotate k).take i := by
    intro i hi
    rw [hdrop, take_take, Nat.min_eq_left hi]
  constructor
  · rintro ⟨hpos, -⟩
    have key : ∀ j < k, prefHeight w k + 1 ≤ prefHeight w j := by
      intro j hj
      have hj' : j < w.length := lt_of_lt_of_le hj hk2
      set i := j + (w.length - k) with hi
      have hile : i ≤ w.length - 1 := by omega
      have h1 := hpos i
      rw [htake i hile] at h1
      rw [dyckHeight_take_rotate_of_ge hk2 (by omega) (by omega), hw] at h1
      have : i - (w.length - k) = j := by omega
      rw [this] at h1
      omega
    refine ⟨fun j hj ↦ ?_, fun j hj ↦ by have := key j hj; omega⟩
    rcases lt_or_ge j k with hjk | hjk
    · have := key j hjk
      omega
    · set i := j - k with hi
      have hile : i ≤ w.length - 1 := by omega
      have h1 := hpos i
      rw [htake i hile, dyckHeight_take_rotate_of_le hk2 (by omega)] at h1
      have : k + i = j := by omega
      rw [this] at h1
      omega
  · rintro ⟨hmin, hlt⟩
    have hstrict : ∀ j < k, prefHeight w k + 1 ≤ prefHeight w j := fun j hj ↦ by
      have := hlt j hj; omega
    have hlast : dyckHeight ((w.rotate k).take (w.length - 1)) = 0 := by
      rcases le_or_gt (w.length - 1) (w.length - k) with hc | hc
      · have hk1' : k = 1 := by omega
        subst hk1'
        rw [dyckHeight_take_rotate_of_le hk2 (by omega)]
        have h1 : 1 + (w.length - 1) = w.length := by omega
        rw [h1, prefHeight_length, hw]
        have h2 : prefHeight w 1 ≤ -1 := by
          have := hmin w.length le_rfl
          rwa [prefHeight_length, hw] at this
        have h3 := prefHeight_le_prefHeight_succ_add_one w 0
        rw [prefHeight_zero, Nat.zero_add] at h3
        omega
      · rw [dyckHeight_take_rotate_of_ge hk2 (by omega) (by omega), hw]
        have h1 : w.length - 1 - (w.length - k) = k - 1 := by omega
        rw [h1]
        have h2 := hstrict (k - 1) (by omega)
        have h3 := prefHeight_le_prefHeight_succ_add_one w (k - 1)
        have h4 : k - 1 + 1 = k := by omega
        rw [h4] at h3
        omega
    refine ⟨fun i ↦ ?_, ?_⟩
    · rcases le_or_gt i (w.length - 1) with hi | hi
      · rw [htake i hi]
        rcases le_or_gt i (w.length - k) with hc | hc
        · rw [dyckHeight_take_rotate_of_le hk2 hc]
          have := hmin (k + i) (by omega)
          omega
        · rw [dyckHeight_take_rotate_of_ge hk2 (by omega) (by omega), hw]
          have := hstrict (i - (w.length - k)) (by omega)
          omega
      · rw [take_of_length_le (by omega), hdrop, hlast]
    · rw [hdrop, hlast]

/-- The **cycle lemma**: a word of height `-1` has exactly one rotation which is a Dyck word
followed by a final `D`. -/
theorem existsUnique_isDyckWord_dropLast_rotate {w : List DyckStep} (hw : dyckHeight w = -1) :
    ∃! k, (1 ≤ k ∧ k ≤ w.length) ∧ IsDyckWord ((w.rotate k).dropLast) := by
  have hne : w ≠ [] := by
    rintro rfl
    simp at hw
  have hm : 1 ≤ w.length := length_pos_iff.2 hne
  have hfm := isFirstMin_firstMinIdx w
  have hk2 : firstMinIdx w ≤ w.length := hfm.le_length
  have hk1 : 1 ≤ firstMinIdx w := by
    rcases Nat.eq_zero_or_pos (firstMinIdx w) with h0 | h
    · exfalso
      have := hfm.1 w.length le_rfl
      rw [h0, prefHeight_zero, prefHeight_length, hw] at this
      omega
    · exact h
  refine ⟨firstMinIdx w, ⟨⟨hk1, hk2⟩, (isDyckWord_dropLast_rotate_iff hw hk1 hk2).2 hfm⟩, ?_⟩
  rintro k ⟨⟨hj1, hj2⟩, hk⟩
  exact ((isDyckWord_dropLast_rotate_iff hw hj1 hj2).1 hk).unique hfm |>.symm ▸ rfl

/-- The rotation at the first minimum of a word of height `-1` ends with a `D`. -/
lemma dropLast_rotate_concat {w : List DyckStep} (hw : dyckHeight w = -1) {k : ℕ}
    (hk : IsDyckWord ((w.rotate k).dropLast)) : (w.rotate k).dropLast ++ [D] = w.rotate k := by
  have hne : w ≠ [] := by
    rintro rfl
    simp at hw
  have hne' : w.rotate k ≠ [] := by
    intro h
    exact hne (by simpa using congrArg List.length h)
  have hsplit := dropLast_append_getLast hne'
  have hh : dyckHeight (w.rotate k) = -1 := by rw [dyckHeight_rotate, hw]
  have h1 : dyckHeight ((w.rotate k).dropLast) + dyckHeight [(w.rotate k).getLast hne'] = -1 := by
    rw [← dyckHeight_append, hsplit, hh]
  rw [hk.2] at h1
  have h2 : (w.rotate k).getLast hne' = D := by
    rcases DyckStep.dichotomy ((w.rotate k).getLast hne') with h | h <;> rw [h] at h1 <;> simp at h1
    exact h
  rw [← h2]
  exact hsplit

/-! ### Counting the words with a given number of `U`s -/

/-- The number of `U`s of the word `List.ofFn f` is the number of indices sent to `U`. -/
lemma count_U_ofFn : ∀ (m : ℕ) (f : Fin m → DyckStep),
    (List.ofFn f).count U = (univ.filter fun i ↦ f i = U).card := by
  intro m
  induction m with
  | zero => intro f; simp
  | succ m ih =>
    intro f
    rw [List.ofFn_succ, List.count_cons, ih]
    simp only [Finset.card_filter, Fin.sum_univ_succ]
    by_cases h : f 0 = U
    · simp [h]
      omega
    · simp [h]

/-- The words of length `m` are the functions from `Fin m` to the two letters. -/
def wordFinEquiv (m : ℕ) : {w : List DyckStep // w.length = m} ≃ (Fin m → DyckStep) where
  toFun w i := w.1[(i : ℕ)]'(by rw [w.2]; exact i.isLt)
  invFun f := ⟨List.ofFn f, by simp⟩
  left_inv w := by
    ext1
    apply List.ext_getElem (by simp [w.2])
    intro n h1 h2
    simp
  right_inv f := by
    funext i
    simp

lemma ofFn_wordFinEquiv (m : ℕ) (v : {w : List DyckStep // w.length = m}) :
    List.ofFn (wordFinEquiv m v) = v.1 :=
  congrArg Subtype.val ((wordFinEquiv m).symm_apply_apply v)

/-- A word of length `m` is determined by the set of the positions of its `U`s. -/
def stepFunEquivFinset (m : ℕ) : (Fin m → DyckStep) ≃ Finset (Fin m) where
  toFun f := univ.filter fun i ↦ f i = U
  invFun s i := if i ∈ s then U else D
  left_inv f := by
    funext i
    rcases DyckStep.dichotomy (f i) with h | h <;> simp [h]
  right_inv s := by
    ext i
    simp

/-- Words of length `m` with `k` letters `U` are the `k`-element subsets of `Fin m`. -/
def wordsCountEquiv (m k : ℕ) :
    {w : List DyckStep // w.length = m ∧ w.count U = k} ≃ {s : Finset (Fin m) // s.card = k} :=
  let e1 : {w : List DyckStep // w.length = m ∧ w.count U = k} ≃
      {v : {w : List DyckStep // w.length = m} // v.1.count U = k} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm
  let e2 : {v : {w : List DyckStep // w.length = m} // v.1.count U = k} ≃
      {f : Fin m → DyckStep // (univ.filter fun i ↦ f i = U).card = k} :=
    (wordFinEquiv m).subtypeEquiv (fun v ↦ by rw [← ofFn_wordFinEquiv m v, count_U_ofFn])
  let e3 : {f : Fin m → DyckStep // (univ.filter fun i ↦ f i = U).card = k} ≃
      {s : Finset (Fin m) // s.card = k} :=
    (stepFunEquivFinset m).subtypeEquiv (fun f ↦ by simp [stepFunEquivFinset])
  (e1.trans e2).trans e3

instance instFintypeWordsCount (m k : ℕ) :
    Fintype {w : List DyckStep // w.length = m ∧ w.count U = k} :=
  Fintype.ofEquiv _ (wordsCountEquiv m k).symm

/-- There are `m.choose k` words of length `m` with `k` letters `U` (Coq `card_bal_hsz`). -/
theorem card_words_count_eq (m k : ℕ) :
    Fintype.card {w : List DyckStep // w.length = m ∧ w.count U = k} = m.choose k := by
  rw [Fintype.card_congr (wordsCountEquiv m k), Fintype.card_finset_len, Fintype.card_fin]

/-! ### The rotation bijection and the Catalan numbers -/

/-- A word with one more `D` than `U`s has height `-1`. -/
lemma dyckHeight_eq_neg_one {w : List DyckStep} {n : ℕ} (hl : w.length = 2 * n + 1)
    (hc : w.count U = n) : dyckHeight w = -1 := by
  have h := length_eq_count_add_count w
  rw [hl, hc] at h
  simp only [dyckHeight, hc]
  omega

/-- A Dyck word of length `2 * n` has `n` letters `U`. -/
lemma count_U_of_isDyckWord {d : List DyckStep} {n : ℕ} (hd : IsDyckWord d)
    (hl : d.length = 2 * n) : d.count U = n := by
  have h1 := length_eq_count_add_count d
  have h2 := (dyckHeight_eq_zero_iff d).1 hd.2
  omega

lemma one_le_firstMinIdx {w : List DyckStep} (hw : dyckHeight w = -1) : 1 ≤ firstMinIdx w := by
  rcases Nat.eq_zero_or_pos (firstMinIdx w) with h0 | h
  · exfalso
    have h1 := (isFirstMin_firstMinIdx w).1 w.length le_rfl
    rw [h0, prefHeight_zero, prefHeight_length, hw] at h1
    omega
  · exact h

lemma firstMinIdx_le_length (w : List DyckStep) : firstMinIdx w ≤ w.length :=
  (isFirstMin_firstMinIdx w).le_length

lemma isDyckWord_dropLast_rotate_firstMinIdx {w : List DyckStep} (hw : dyckHeight w = -1) :
    IsDyckWord ((w.rotate (firstMinIdx w)).dropLast) :=
  (isDyckWord_dropLast_rotate_iff hw (one_le_firstMinIdx hw) (firstMinIdx_le_length w)).2
    (isFirstMin_firstMinIdx w)

/-- The bijection given by the cycle lemma: a word of length `2 * n + 1` with `n` letters `U`
is the same thing as a Dyck word of length `2 * n` together with a rotation index. -/
noncomputable def cycleEquiv (n : ℕ) :
    {w : List DyckStep // w.length = 2 * n + 1 ∧ w.count U = n} ≃
      {d : List DyckStep // IsDyckWord d ∧ d.length = 2 * n} × Fin (2 * n + 1) where
  toFun w :=
    (⟨(w.1.rotate (firstMinIdx w.1)).dropLast,
      isDyckWord_dropLast_rotate_firstMinIdx (dyckHeight_eq_neg_one w.2.1 w.2.2), by
        rw [length_dropLast, length_rotate, w.2.1]
        omega⟩,
      ⟨firstMinIdx w.1 - 1, by
        have := firstMinIdx_le_length w.1
        rw [w.2.1] at this
        omega⟩)
  invFun p := ⟨(p.1.1 ++ [D]).rotate (2 * n + 1 - (p.2 + 1)), by
      constructor
      · rw [length_rotate, length_append, p.1.2.2]
        simp
      · rw [((p.1.1 ++ [D]).rotate_perm _).count_eq, count_append,
          count_U_of_isDyckWord p.1.2.1 p.1.2.2]
        simp⟩
  left_inv w := by
    obtain ⟨w, hl, hc⟩ := w
    have hw := dyckHeight_eq_neg_one hl hc
    have hk1 := one_le_firstMinIdx hw
    have hk2 := firstMinIdx_le_length w
    rw [hl] at hk2
    ext1
    have hcat := dropLast_rotate_concat hw (isDyckWord_dropLast_rotate_firstMinIdx hw)
    have hidx : 2 * n + 1 - (firstMinIdx w - 1 + 1) = 2 * n + 1 - firstMinIdx w := by omega
    simp only [hidx]
    rw [hcat, rotate_rotate]
    have : firstMinIdx w + (2 * n + 1 - firstMinIdx w) = w.length := by omega
    rw [this, rotate_length]
  right_inv p := by
    obtain ⟨⟨d, hd, hdl⟩, j, hj⟩ := p
    set w := (d ++ [D]).rotate (2 * n + 1 - (j + 1)) with hwdef
    have hlen : w.length = 2 * n + 1 := by
      rw [hwdef, length_rotate, length_append, hdl]
      simp
    have hcount : w.count U = n := by
      rw [hwdef, ((d ++ [D]).rotate_perm _).count_eq, count_append,
        count_U_of_isDyckWord hd hdl]
      simp
    have hw := dyckHeight_eq_neg_one hlen hcount
    have hrot : w.rotate (j + 1) = d ++ [D] := by
      rw [hwdef, rotate_rotate]
      have h1 : 2 * n + 1 - (j + 1) + (j + 1) = (d ++ [D]).length := by
        rw [length_append, hdl]
        simp
        omega
      rw [h1, rotate_length]
    have hdyck : IsDyckWord ((w.rotate (j + 1)).dropLast) := by
      rw [hrot, dropLast_concat]
      exact hd
    have hidx : firstMinIdx w = j + 1 :=
      firstMinIdx_eq_of_isFirstMin
        ((isDyckWord_dropLast_rotate_iff hw (by omega) (by rw [hlen]; omega)).1 hdyck)
    refine Prod.ext (Subtype.ext ?_) (Fin.ext ?_)
    · simp only [← hwdef, hidx, hrot, dropLast_concat]
    · simp only [← hwdef, hidx]
      omega

/-- The Catalan formula obtained from the cycle lemma: there are
`(2 * n + 1).choose n / (2 * n + 1)` Dyck words of length `2 * n` (Coq `card_Dyck_hsz`). -/
theorem succ_two_mul_catalan_eq_choose (n : ℕ) :
    (2 * n + 1) * catalan n = (2 * n + 1).choose n := by
  have h2 := Fintype.card_congr (cycleEquiv n)
  rw [card_words_count_eq, Fintype.card_prod, card_isDyckWord_length_eq_catalan,
    Fintype.card_fin] at h2
  rw [mul_comm]
  exact h2.symm

/-- The balanced words of length `2 * n` are `n + 1` times as many as the Dyck words of the same
length (Coq `card_bal_Dyck_hsz`). -/
theorem card_balanced_eq_succ_mul_catalan (n : ℕ) :
    Fintype.card {w : List DyckStep // w.length = 2 * n ∧ w.count U = n} = (n + 1) * catalan n := by
  rw [card_words_count_eq, ← Nat.centralBinom, succ_mul_catalan_eq_centralBinom]

end List
