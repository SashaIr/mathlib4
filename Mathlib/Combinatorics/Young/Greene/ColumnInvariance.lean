/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.Greene.ColumnDefs
import Mathlib.Combinatorics.Young.Greene.Invariance

/-!
# Greene column invariants are plactic invariants

A Lean 4 port of the column case of `theories/LRrule/Greene_inv.v` from
[Coq-Combi](https://github.com/math-comp/Coq-Combi).

We show that the Greene column invariants `List.greeneCol w k` (the maximal number of
letters of `w` covered by `k` strictly decreasing subsequences) do not change under the
elementary Knuth transformations, hence are invariants of the plactic class of a word.

## Main results

* `List.greeneCol_placticEquiv` : Knuth equivalent words have the same Greene column
  invariants (Coq `Greene_col_invar_plactic`).
-/

namespace List

open List

variable {T : Type*} [LinearOrder T]

/-! ### Transferring a strictly decreasing colouring -/

/-- The key transfer lemma for strictly decreasing colourings: a colouring of
`p ++ mu ++ s` yields a colouring of `p ++ mv ++ s`, provided the four families of
comparisons hold. -/
lemma isGreeneDecCol_mixCol {k : ℕ} {p s mu mv : List T} {c wc : ℕ → Option ℕ} {τ : ℕ → ℕ}
    (hmu : mu.length = 3) (hmv : mv.length = 3)
    (hc : IsGreeneDecCol (p ++ mu ++ s) k c)
    (hτinj : Function.Injective τ) (hτk : ∀ x, x < k → τ x < k)
    (hwck : ∀ j x, j < 3 → wc j = some x → x < k)
    (h11 : ∀ i j x (hij : i < j) (hj : j < 3), wc i = some x → wc j = some x →
      mv[j]'(by omega) < mv[i]'(by omega))
    (h12 : ∀ i j x (hi : i < p.length) (hj : j < 3), c i = some x → wc j = some x →
      mv[j]'(by omega) < p[i])
    (h23 : ∀ j i x (hj : j < 3) (hi : i < s.length), wc j = some x →
      (c (p.length + 3 + i)).map τ = some x → s[i] < mv[j]'(by omega))
    (h13 : ∀ i j x (hi : i < p.length) (hj : j < s.length), c i = some x →
      (c (p.length + 3 + j)).map τ = some x → s[j] < p[i]) :
    IsGreeneDecCol (p ++ mv ++ s) k (mixCol p.length c wc τ) := by
  constructor
  · intro i x hx
    rcases lt_or_ge i p.length with hi | hi
    · exact hc.lt_of_colour (by rwa [mixCol_lt hi] at hx)
    · by_cases hi3 : i < p.length + 3
      · have : i = p.length + (i - p.length) := by omega
        rw [this, mixCol_mid (by omega)] at hx
        exact hwck _ x (by omega) hx
      · rw [mixCol_gt (by omega)] at hx
        obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
        exact hτk _ (hc.lt_of_colour hy)
  · intro i j x hij hj hci hcj
    have hlenv : (p ++ mv ++ s).length = p.length + 3 + s.length := by
      rw [length_append_mid, hmv]
    have hlenu : (p ++ mu ++ s).length = p.length + 3 + s.length := by
      rw [length_append_mid, hmu]
    have hj' : j < p.length + 3 + s.length := hlenv ▸ hj
    rcases lt_or_ge i p.length with hi | hi
    · rw [mixCol_lt hi] at hci
      have hvi : (p ++ mv ++ s)[i]'(hij.trans hj) = p[i] :=
        getElem_mid_left' p mv s hi _
      rcases lt_or_ge j p.length with hjp | hjp
      · rw [mixCol_lt hjp] at hcj
        have hvj : (p ++ mv ++ s)[j]'hj = p[j] := getElem_mid_left' p mv s hjp _
        have hui : (p ++ mu ++ s)[i]'(by omega) = p[i] := getElem_mid_left' p mu s hi _
        have huj : (p ++ mu ++ s)[j]'(by omega) = p[j] := getElem_mid_left' p mu s hjp _
        have hlt := hc.gt_of_colour hij (show j < (p ++ mu ++ s).length by omega) hci hcj
        exact (hvj.trans_lt (huj.symm.trans_lt (hlt.trans_eq hui))).trans_eq hvi.symm
      · by_cases hj3 : j < p.length + 3
        · have hjeq : j = p.length + (j - p.length) := by omega
          have hcj' : wc (j - p.length) = some x := by
            rw [hjeq, mixCol_mid (by omega)] at hcj; exact hcj
          have hvj : (p ++ mv ++ s)[j]'hj = mv[j - p.length]'(by omega) :=
            getElem_mid_mid' p mv s (by omega) hjeq _
          exact (hvj.trans_lt
            (h12 i (j - p.length) x hi (by omega) hci hcj')).trans_eq hvi.symm
        · have hjeq : j = p.length + 3 + (j - p.length - 3) := by omega
          have hcj' : (c (p.length + 3 + (j - p.length - 3))).map τ = some x := by
            rw [mixCol_gt (by omega : p.length + 3 ≤ j)] at hcj
            rw [← hjeq]; exact hcj
          have hvj : (p ++ mv ++ s)[j]'hj = s[j - p.length - 3]'(by omega) :=
            getElem_mid_right' p mv s (by omega) (by omega) _
          exact (hvj.trans_lt
            (h13 i (j - p.length - 3) x hi (by omega) hci hcj')).trans_eq hvi.symm
    · by_cases hi3 : i < p.length + 3
      · have hieq : i = p.length + (i - p.length) := by omega
        have hci' : wc (i - p.length) = some x := by
          rw [hieq, mixCol_mid (by omega)] at hci; exact hci
        have hvi : (p ++ mv ++ s)[i]'(hij.trans hj) = mv[i - p.length]'(by omega) :=
          getElem_mid_mid' p mv s (by omega) hieq _
        by_cases hj3 : j < p.length + 3
        · have hjeq : j = p.length + (j - p.length) := by omega
          have hcj' : wc (j - p.length) = some x := by
            rw [hjeq, mixCol_mid (by omega)] at hcj; exact hcj
          have hvj : (p ++ mv ++ s)[j]'hj = mv[j - p.length]'(by omega) :=
            getElem_mid_mid' p mv s (by omega) hjeq _
          exact (hvj.trans_lt
            (h11 (i - p.length) (j - p.length) x (by omega) (by omega) hci' hcj')).trans_eq
              hvi.symm
        · have hjeq : j = p.length + 3 + (j - p.length - 3) := by omega
          have hcj' : (c (p.length + 3 + (j - p.length - 3))).map τ = some x := by
            rw [mixCol_gt (by omega : p.length + 3 ≤ j)] at hcj
            rw [← hjeq]; exact hcj
          have hvj : (p ++ mv ++ s)[j]'hj = s[j - p.length - 3]'(by omega) :=
            getElem_mid_right' p mv s (by omega) (by omega) _
          exact (hvj.trans_lt
            (h23 (i - p.length) (j - p.length - 3) x (by omega) (by omega) hci' hcj')).trans_eq
              hvi.symm
      · rw [mixCol_gt (by omega)] at hci
        rw [mixCol_gt (by omega)] at hcj
        obtain ⟨y, hy, hxy⟩ := Option.map_eq_some_iff.1 hci
        obtain ⟨y', hy', hxy'⟩ := Option.map_eq_some_iff.1 hcj
        have hyy : y = y' := hτinj (hxy.trans hxy'.symm)
        subst hyy
        have hvi : (p ++ mv ++ s)[i]'(hij.trans hj) = s[i - p.length - 3]'(by omega) :=
          getElem_mid_right' p mv s (by omega) (by omega) _
        have hvj : (p ++ mv ++ s)[j]'hj = s[j - p.length - 3]'(by omega) :=
          getElem_mid_right' p mv s (by omega) (by omega) _
        have hui : (p ++ mu ++ s)[i]'(by omega) = s[i - p.length - 3]'(by omega) :=
          getElem_mid_right' p mu s (by omega) (by omega) _
        have huj : (p ++ mu ++ s)[j]'(by omega) = s[j - p.length - 3]'(by omega) :=
          getElem_mid_right' p mu s (by omega) (by omega) _
        have hlt := hc.gt_of_colour hij (show j < (p ++ mu ++ s).length by omega) hy hy'
        exact (hvj.trans_lt (huj.symm.trans_lt (hlt.trans_eq hui))).trans_eq hvi.symm

/-! ### The comparisons satisfied by a strictly decreasing colouring -/

section Facts

variable {k : ℕ} {p s m : List T} {c : ℕ → Option ℕ}

lemma dcol_pre_mid (hm : m.length = 3) (hc : IsGreeneDecCol (p ++ m ++ s) k c)
    {i j x : ℕ} (hi : i < p.length) (hj : j < 3) (hci : c i = some x)
    (hcj : c (p.length + j) = some x) : m[j]'(by omega) < p[i] := by
  have hlen : (p ++ m ++ s).length = p.length + 3 + s.length := by rw [length_append_mid, hm]
  have hui : (p ++ m ++ s)[i]'(by omega) = p[i] := getElem_mid_left' p m s hi _
  have huj : (p ++ m ++ s)[p.length + j]'(by omega) = m[j]'(by omega) :=
    getElem_mid_mid' p m s (by omega) rfl _
  have hlt := hc.gt_of_colour (show i < p.length + j by omega)
    (show p.length + j < (p ++ m ++ s).length by omega) hci hcj
  exact (huj.symm.trans_lt hlt).trans_eq hui

lemma dcol_mid_mid (hm : m.length = 3) (hc : IsGreeneDecCol (p ++ m ++ s) k c)
    {i j x : ℕ} (hij : i < j) (hj : j < 3) (hci : c (p.length + i) = some x)
    (hcj : c (p.length + j) = some x) : m[j]'(by omega) < m[i]'(by omega) := by
  have hlen : (p ++ m ++ s).length = p.length + 3 + s.length := by rw [length_append_mid, hm]
  have hui : (p ++ m ++ s)[p.length + i]'(by omega) = m[i]'(by omega) :=
    getElem_mid_mid' p m s (by omega) rfl _
  have huj : (p ++ m ++ s)[p.length + j]'(by omega) = m[j]'(by omega) :=
    getElem_mid_mid' p m s (by omega) rfl _
  have hlt := hc.gt_of_colour (show p.length + i < p.length + j by omega)
    (show p.length + j < (p ++ m ++ s).length by omega) hci hcj
  exact (huj.symm.trans_lt hlt).trans_eq hui

lemma dcol_mid_suf (hm : m.length = 3) (hc : IsGreeneDecCol (p ++ m ++ s) k c)
    {j i x : ℕ} (hj : j < 3) (hi : i < s.length) (hcj : c (p.length + j) = some x)
    (hci : c (p.length + 3 + i) = some x) : s[i] < m[j]'(by omega) := by
  have hlen : (p ++ m ++ s).length = p.length + 3 + s.length := by rw [length_append_mid, hm]
  have huj : (p ++ m ++ s)[p.length + j]'(by omega) = m[j]'(by omega) :=
    getElem_mid_mid' p m s (by omega) rfl _
  have hui : (p ++ m ++ s)[p.length + 3 + i]'(by omega) = s[i] :=
    getElem_mid_right' p m s hi (by omega) _
  have hlt := hc.gt_of_colour (show p.length + j < p.length + 3 + i by omega)
    (show p.length + 3 + i < (p ++ m ++ s).length by omega) hcj hci
  exact (hui.symm.trans_lt hlt).trans_eq huj

lemma dcol_pre_suf (hm : m.length = 3) (hc : IsGreeneDecCol (p ++ m ++ s) k c)
    {i j x : ℕ} (hi : i < p.length) (hj : j < s.length) (hci : c i = some x)
    (hcj : c (p.length + 3 + j) = some x) : s[j] < p[i] := by
  have hlen : (p ++ m ++ s).length = p.length + 3 + s.length := by rw [length_append_mid, hm]
  have hui : (p ++ m ++ s)[i]'(by omega) = p[i] := getElem_mid_left' p m s hi _
  have huj : (p ++ m ++ s)[p.length + 3 + j]'(by omega) = s[j] :=
    getElem_mid_right' p m s hj (by omega) _
  have hlt := hc.gt_of_colour (show i < p.length + 3 + j by omega)
    (show p.length + 3 + j < (p ++ m ++ s).length by omega) hci hcj
  exact (huj.symm.trans_lt hlt).trans_eq hui

end Facts

/-- Combination of `isGreeneDecCol_mixCol` and `greeneSize_mixCol`. -/
lemma greeneSize_le_greeneCol_mix {k : ℕ} {p s mu mv : List T} {c wc : ℕ → Option ℕ} {τ : ℕ → ℕ}
    (hmu : mu.length = 3) (hmv : mv.length = 3)
    (hc : IsGreeneDecCol (p ++ mu ++ s) k c)
    (hτinj : Function.Injective τ) (hτk : ∀ x, x < k → τ x < k)
    (hwck : ∀ j x, j < 3 → wc j = some x → x < k)
    (h11 : ∀ i j x (hij : i < j) (hj : j < 3), wc i = some x → wc j = some x →
      mv[j]'(by omega) < mv[i]'(by omega))
    (h12 : ∀ i j x (hi : i < p.length) (hj : j < 3), c i = some x → wc j = some x →
      mv[j]'(by omega) < p[i])
    (h23 : ∀ j i x (hj : j < 3) (hi : i < s.length), wc j = some x →
      (c (p.length + 3 + i)).map τ = some x → s[i] < mv[j]'(by omega))
    (h13 : ∀ i j x (hi : i < p.length) (hj : j < s.length), c i = some x →
      (c (p.length + 3 + j)).map τ = some x → s[j] < p[i])
    (hcount : ((Finset.range 3).filter fun j => (wc j).isSome).card =
      ((Finset.range 3).filter fun j => (c (p.length + j)).isSome).card) :
    greeneSize (p ++ mu ++ s) c ≤ greeneCol (p ++ mv ++ s) k := by
  rw [← greeneSize_mixCol (mu := mu) (mv := mv) (τ := τ) hmu hmv hcount]
  exact le_greeneCol (isGreeneDecCol_mixCol hmu hmv hc hτinj hτk hwck h11 h12 h23 h13)

/-! ### The four elementary Knuth moves: the easy directions -/

/-- The easy direction of the first Knuth relation: the three letters keep their colours. -/
lemma greeneCol_knuthAC_le {k : ℕ} (p s : List T) {X Y Z : T} (hXY : X ≤ Y) (hYZ : Y < Z) :
    greeneCol (p ++ [X, Z, Y] ++ s) k ≤ greeneCol (p ++ [Z, X, Y] ++ s) k := by
  refine greeneCol_le fun c hc => ?_
  refine greeneSize_le_greeneCol_mix (mv := [Z, X, Y]) (τ := id)
    (wc := fun j => if j = 0 then c (p.length + 1) else if j = 1 then c (p.length + 0)
      else c (p.length + 2)) rfl rfl hc Function.injective_id (fun _ h => h) ?_ ?_ ?_ ?_ ?_ ?_
  · intro j x _ hwc
    split_ifs at hwc <;> exact hc.lt_of_colour hwc
  · intro i j x hij hj h1 h2
    interval_cases j
    · exact absurd hij (Nat.not_lt_zero i)
    · interval_cases i
      · simpa using lt_of_le_of_lt hXY hYZ
    · interval_cases i
      · simpa using hYZ
      · rw [ite_eq_right (by norm_num), ite_eq_left rfl] at h1
        rw [ite_eq_right (by norm_num), ite_eq_right (by norm_num)] at h2
        have := dcol_mid_mid (m := [X, Z, Y]) rfl hc (i := 0) (j := 2) (by norm_num)
          (by norm_num) h1 h2
        simpa using this
  · intro i j x hi hj hci hwc
    interval_cases j
    · rw [ite_eq_left rfl] at hwc
      simpa using dcol_pre_mid (m := [X, Z, Y]) rfl hc hi (show (1:ℕ) < 3 by norm_num) hci hwc
    · rw [ite_eq_right (by norm_num), ite_eq_left rfl] at hwc
      simpa using dcol_pre_mid (m := [X, Z, Y]) rfl hc hi (show (0:ℕ) < 3 by norm_num) hci hwc
    · rw [ite_eq_right (by norm_num), ite_eq_right (by norm_num)] at hwc
      simpa using dcol_pre_mid (m := [X, Z, Y]) rfl hc hi (show (2:ℕ) < 3 by norm_num) hci hwc
  · intro j i x hj hi hwc hcs
    rw [Option.map_id] at hcs
    interval_cases j
    · rw [ite_eq_left rfl] at hwc
      simpa using dcol_mid_suf (m := [X, Z, Y]) rfl hc (show (1:ℕ) < 3 by norm_num) hi hwc hcs
    · rw [ite_eq_right (by norm_num), ite_eq_left rfl] at hwc
      simpa using dcol_mid_suf (m := [X, Z, Y]) rfl hc (show (0:ℕ) < 3 by norm_num) hi hwc hcs
    · rw [ite_eq_right (by norm_num), ite_eq_right (by norm_num)] at hwc
      simpa using dcol_mid_suf (m := [X, Z, Y]) rfl hc (show (2:ℕ) < 3 by norm_num) hi hwc hcs
  · intro i j x hi hj hci hcs
    rw [Option.map_id] at hcs
    exact dcol_pre_suf (m := [X, Z, Y]) rfl hc hi hj hci hcs
  · simp only [card_filter_range3]
    norm_num
    split_ifs <;> omega

/-- The easy direction of the second Knuth relation: the three letters keep their colours. -/
lemma greeneCol_knuthCA_le {k : ℕ} (p s : List T) {X Y Z : T} (hXY : X < Y) (hYZ : Y ≤ Z) :
    greeneCol (p ++ [Y, X, Z] ++ s) k ≤ greeneCol (p ++ [Y, Z, X] ++ s) k := by
  refine greeneCol_le fun c hc => ?_
  refine greeneSize_le_greeneCol_mix (mv := [Y, Z, X]) (τ := id)
    (wc := fun j => if j = 0 then c (p.length + 0) else if j = 1 then c (p.length + 2)
      else c (p.length + 1)) rfl rfl hc Function.injective_id (fun _ h => h) ?_ ?_ ?_ ?_ ?_ ?_
  · intro j x _ hwc
    split_ifs at hwc <;> exact hc.lt_of_colour hwc
  · intro i j x hij hj h1 h2
    interval_cases j
    · exact absurd hij (Nat.not_lt_zero i)
    · interval_cases i
      · rw [ite_eq_left rfl] at h1
        rw [ite_eq_right (by norm_num), ite_eq_left rfl] at h2
        have := dcol_mid_mid (m := [Y, X, Z]) rfl hc (i := 0) (j := 2) (by norm_num)
          (by norm_num) h1 h2
        simpa using this
    · interval_cases i
      · simpa using hXY
      · simpa using lt_of_lt_of_le hXY hYZ
  · intro i j x hi hj hci hwc
    interval_cases j
    · rw [ite_eq_left rfl] at hwc
      simpa using dcol_pre_mid (m := [Y, X, Z]) rfl hc hi (show (0:ℕ) < 3 by norm_num) hci hwc
    · rw [ite_eq_right (by norm_num), ite_eq_left rfl] at hwc
      simpa using dcol_pre_mid (m := [Y, X, Z]) rfl hc hi (show (2:ℕ) < 3 by norm_num) hci hwc
    · rw [ite_eq_right (by norm_num), ite_eq_right (by norm_num)] at hwc
      simpa using dcol_pre_mid (m := [Y, X, Z]) rfl hc hi (show (1:ℕ) < 3 by norm_num) hci hwc
  · intro j i x hj hi hwc hcs
    rw [Option.map_id] at hcs
    interval_cases j
    · rw [ite_eq_left rfl] at hwc
      simpa using dcol_mid_suf (m := [Y, X, Z]) rfl hc (show (0:ℕ) < 3 by norm_num) hi hwc hcs
    · rw [ite_eq_right (by norm_num), ite_eq_left rfl] at hwc
      simpa using dcol_mid_suf (m := [Y, X, Z]) rfl hc (show (2:ℕ) < 3 by norm_num) hi hwc hcs
    · rw [ite_eq_right (by norm_num), ite_eq_right (by norm_num)] at hwc
      simpa using dcol_mid_suf (m := [Y, X, Z]) rfl hc (show (1:ℕ) < 3 by norm_num) hi hwc hcs
  · intro i j x hi hj hci hcs
    rw [Option.map_id] at hcs
    exact dcol_pre_suf (m := [Y, X, Z]) rfl hc hi hj hci hcs
  · simp only [card_filter_range3]
    norm_num
    split_ifs <;> omega

/-! ### The first Knuth relation: the hard direction -/

/-- The hard direction of the first Knuth relation. -/
lemma greeneCol_knuthAC_ge {k : ℕ} (p s : List T) {X Y Z : T} (hXY : X ≤ Y) (hYZ : Y < Z) :
    greeneCol (p ++ [Z, X, Y] ++ s) k ≤ greeneCol (p ++ [X, Z, Y] ++ s) k := by
  refine greeneCol_le fun c hc => ?_
  by_cases hgen : ∃ g, c (p.length + 0) = some g ∧ c (p.length + 1) = some g
  · obtain ⟨g, hg0, hg1⟩ := hgen
    cases hc2 : c (p.length + 2) with
    | none =>
      -- the third letter is not coloured: `X` is dropped and `g` takes `Z` and `Y`
      refine greeneSize_le_greeneCol_mix (mv := [X, Z, Y]) (τ := id)
        (wc := fun j => if j = 0 then none else some g) rfl rfl hc Function.injective_id
        (fun _ h => h) ?_ ?_ ?_ ?_ ?_ ?_
      · intro j x _ hwc
        split_ifs at hwc
        obtain rfl : x = g := by simpa using hwc.symm
        exact hc.lt_of_colour hg0
      · intro i j x hij hj h1 h2
        interval_cases j
        · exact absurd hij (Nat.not_lt_zero i)
        · interval_cases i
          · simp at h1
        · interval_cases i
          · simp at h1
          · simpa using hYZ
      · intro i j x hi hj hci hwc
        interval_cases j
        · simp at hwc
        · obtain rfl : x = g := by simpa using hwc.symm
          simpa using dcol_pre_mid (m := [Z, X, Y]) rfl hc hi (show (0:ℕ) < 3 by norm_num)
            hci hg0
        · obtain rfl : x = g := by simpa using hwc.symm
          have := dcol_pre_mid (m := [Z, X, Y]) rfl hc hi (show (0:ℕ) < 3 by norm_num) hci hg0
          simp only [List.getElem_cons_zero] at this
          simpa using hYZ.trans this
      · intro j i x hj hi hwc hcs
        rw [Option.map_id] at hcs
        interval_cases j
        · simp at hwc
        · obtain rfl : x = g := by simpa using hwc.symm
          have := dcol_mid_suf (m := [Z, X, Y]) rfl hc (show (1:ℕ) < 3 by norm_num) hi hg1 hcs
          simp only [List.getElem_cons_zero, List.getElem_cons_succ] at this
          simpa using this.trans_le (hXY.trans hYZ.le)
        · obtain rfl : x = g := by simpa using hwc.symm
          have := dcol_mid_suf (m := [Z, X, Y]) rfl hc (show (1:ℕ) < 3 by norm_num) hi hg1 hcs
          simp only [List.getElem_cons_zero, List.getElem_cons_succ] at this
          simpa using this.trans_le hXY
      · intro i j x hi hj hci hcs
        rw [Option.map_id] at hcs
        exact dcol_pre_suf (m := [Z, X, Y]) rfl hc hi hj hci hcs
      · simp only [card_filter_range3, hg0, hg1, hc2]
        norm_num
    | some h =>
      -- all three letters are coloured: `X` takes the colour of `Y`, and `g` takes `Z` and `Y`
      have hgh : g ≠ h := by
        rintro rfl
        have := dcol_mid_mid (m := [Z, X, Y]) rfl hc (i := 1) (j := 2) (by norm_num)
          (by norm_num) hg1 hc2
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at this
        exact absurd this (not_lt.2 hXY)
      refine greeneSize_le_greeneCol_mix (mv := [X, Z, Y]) (τ := swapNat g h)
        (wc := fun j => if j = 0 then some h else some g) rfl rfl hc (swapNat_injective g h)
        (fun x hx => swapNat_lt (hc.lt_of_colour hg0) (hc.lt_of_colour hc2) hx) ?_ ?_ ?_ ?_ ?_ ?_
      · intro j x _ hwc
        split_ifs at hwc
        · obtain rfl : x = h := by simpa using hwc.symm
          exact hc.lt_of_colour hc2
        · obtain rfl : x = g := by simpa using hwc.symm
          exact hc.lt_of_colour hg0
      · intro i j x hij hj h1 h2
        interval_cases j
        · exact absurd hij (Nat.not_lt_zero i)
        · interval_cases i
          · simp only [ite_eq_right (by norm_num : ¬(1:ℕ) = 0)] at h1 h2
            exact absurd ((Option.some.inj h2).trans (Option.some.inj h1).symm) hgh
        · interval_cases i
          · simp only [ite_eq_right (by norm_num : ¬(2:ℕ) = 0)] at h1 h2
            exact absurd ((Option.some.inj h2).trans (Option.some.inj h1).symm) hgh
          · simpa using hYZ
      · intro i j x hi hj hci hwc
        interval_cases j
        · obtain rfl : x = h := by simpa using hwc.symm
          have := dcol_pre_mid (m := [Z, X, Y]) rfl hc hi (show (2:ℕ) < 3 by norm_num) hci hc2
          simp only [List.getElem_cons_zero, List.getElem_cons_succ] at this
          simpa using hXY.trans_lt this
        · obtain rfl : x = g := by simpa using hwc.symm
          simpa using dcol_pre_mid (m := [Z, X, Y]) rfl hc hi (show (0:ℕ) < 3 by norm_num)
            hci hg0
        · obtain rfl : x = g := by simpa using hwc.symm
          have := dcol_pre_mid (m := [Z, X, Y]) rfl hc hi (show (0:ℕ) < 3 by norm_num) hci hg0
          simp only [List.getElem_cons_zero] at this
          simpa using hYZ.trans this
      · intro j i x hj hi hwc hcs
        have hcs2 := map_swapNat_eq_some hcs
        interval_cases j
        · obtain rfl : x = h := by simpa using hwc.symm
          rw [swapNat_right] at hcs2
          simpa using dcol_mid_suf (m := [Z, X, Y]) rfl hc (show (1:ℕ) < 3 by norm_num) hi hg1
            hcs2
        · obtain rfl : x = g := by simpa using hwc.symm
          rw [swapNat_left] at hcs2
          have := dcol_mid_suf (m := [Z, X, Y]) rfl hc (show (2:ℕ) < 3 by norm_num) hi hc2 hcs2
          simp only [List.getElem_cons_zero, List.getElem_cons_succ] at this
          simpa using this.trans hYZ
        · obtain rfl : x = g := by simpa using hwc.symm
          rw [swapNat_left] at hcs2
          simpa using dcol_mid_suf (m := [Z, X, Y]) rfl hc (show (2:ℕ) < 3 by norm_num) hi hc2
            hcs2
      · intro i j x hi hj hci hcs
        have hcs2 := map_swapNat_eq_some hcs
        by_cases hxg : x = g
        · subst hxg
          rw [swapNat_left] at hcs2
          have h1 := dcol_pre_mid (m := [Z, X, Y]) rfl hc hi (show (0:ℕ) < 3 by norm_num) hci hg0
          have h2 := dcol_mid_suf (m := [Z, X, Y]) rfl hc (show (2:ℕ) < 3 by norm_num) hj hc2 hcs2
          simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h1 h2
          exact h2.trans (hYZ.trans h1)
        · by_cases hxh : x = h
          · subst hxh
            rw [swapNat_right] at hcs2
            have h1 := dcol_pre_mid (m := [Z, X, Y]) rfl hc hi (show (2:ℕ) < 3 by norm_num) hci hc2
            have h2 := dcol_mid_suf (m := [Z, X, Y]) rfl hc (show (1:ℕ) < 3 by norm_num) hj hg1 hcs2
            simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h1 h2
            exact h2.trans_le (hXY.trans h1.le)
          · rw [swapNat_of_ne hxg hxh] at hcs2
            exact dcol_pre_suf (m := [Z, X, Y]) rfl hc hi hj hci hcs2
      · simp only [card_filter_range3, hg0, hg1, hc2]
        norm_num
  · -- the first two letters do not share a colour : the letters keep their colours
    refine greeneSize_le_greeneCol_mix (mv := [X, Z, Y]) (τ := id)
      (wc := fun j => if j = 0 then c (p.length + 1) else if j = 1 then c (p.length + 0)
        else c (p.length + 2)) rfl rfl hc Function.injective_id (fun _ h => h) ?_ ?_ ?_ ?_ ?_ ?_
    · intro j x _ hwc
      split_ifs at hwc <;> exact hc.lt_of_colour hwc
    · intro i j x hij hj h1 h2
      interval_cases j
      · exact absurd hij (Nat.not_lt_zero i)
      · interval_cases i
        · rw [ite_eq_left rfl] at h1
          rw [ite_eq_right (by norm_num), ite_eq_left rfl] at h2
          exact absurd ⟨x, h2, h1⟩ hgen
      · interval_cases i
        · rw [ite_eq_left rfl] at h1
          rw [ite_eq_right (by norm_num), ite_eq_right (by norm_num)] at h2
          have := dcol_mid_mid (m := [Z, X, Y]) rfl hc (i := 1) (j := 2) (by norm_num)
            (by norm_num) h1 h2
          simpa using this
        · rw [ite_eq_right (by norm_num), ite_eq_left rfl] at h1
          rw [ite_eq_right (by norm_num), ite_eq_right (by norm_num)] at h2
          have := dcol_mid_mid (m := [Z, X, Y]) rfl hc (i := 0) (j := 2) (by norm_num)
            (by norm_num) h1 h2
          simpa using this
    · intro i j x hi hj hci hwc
      interval_cases j
      · rw [ite_eq_left rfl] at hwc
        simpa using dcol_pre_mid (m := [Z, X, Y]) rfl hc hi (show (1:ℕ) < 3 by norm_num) hci hwc
      · rw [ite_eq_right (by norm_num), ite_eq_left rfl] at hwc
        simpa using dcol_pre_mid (m := [Z, X, Y]) rfl hc hi (show (0:ℕ) < 3 by norm_num) hci hwc
      · rw [ite_eq_right (by norm_num), ite_eq_right (by norm_num)] at hwc
        simpa using dcol_pre_mid (m := [Z, X, Y]) rfl hc hi (show (2:ℕ) < 3 by norm_num) hci hwc
    · intro j i x hj hi hwc hcs
      rw [Option.map_id] at hcs
      interval_cases j
      · rw [ite_eq_left rfl] at hwc
        simpa using dcol_mid_suf (m := [Z, X, Y]) rfl hc (show (1:ℕ) < 3 by norm_num) hi hwc hcs
      · rw [ite_eq_right (by norm_num), ite_eq_left rfl] at hwc
        simpa using dcol_mid_suf (m := [Z, X, Y]) rfl hc (show (0:ℕ) < 3 by norm_num) hi hwc hcs
      · rw [ite_eq_right (by norm_num), ite_eq_right (by norm_num)] at hwc
        simpa using dcol_mid_suf (m := [Z, X, Y]) rfl hc (show (2:ℕ) < 3 by norm_num) hi hwc hcs
    · intro i j x hi hj hci hcs
      rw [Option.map_id] at hcs
      exact dcol_pre_suf (m := [Z, X, Y]) rfl hc hi hj hci hcs
    · simp only [card_filter_range3]
      norm_num
      split_ifs <;> omega

/-! ### The second Knuth relation: the hard direction -/

/-- The hard direction of the second Knuth relation. -/
lemma greeneCol_knuthCA_ge {k : ℕ} (p s : List T) {X Y Z : T} (hXY : X < Y) (hYZ : Y ≤ Z) :
    greeneCol (p ++ [Y, Z, X] ++ s) k ≤ greeneCol (p ++ [Y, X, Z] ++ s) k := by
  refine greeneCol_le fun c hc => ?_
  by_cases hgen : ∃ g, c (p.length + 1) = some g ∧ c (p.length + 2) = some g
  · obtain ⟨g, hg1, hg2⟩ := hgen
    cases hc0 : c (p.length + 0) with
    | none =>
      -- the first letter is not coloured: `Z` is dropped and `g` takes `Y` and `X`
      refine greeneSize_le_greeneCol_mix (mv := [Y, X, Z]) (τ := id)
        (wc := fun j => if j = 2 then none else some g) rfl rfl hc Function.injective_id
        (fun _ h => h) ?_ ?_ ?_ ?_ ?_ ?_
      · intro j x _ hwc
        split_ifs at hwc
        obtain rfl : x = g := by simpa using hwc.symm
        exact hc.lt_of_colour hg1
      · intro i j x hij hj h1 h2
        interval_cases j
        · exact absurd hij (Nat.not_lt_zero i)
        · interval_cases i
          · simpa using hXY
        · simp at h2
      · intro i j x hi hj hci hwc
        interval_cases j
        · obtain rfl : x = g := by simpa using hwc.symm
          have := dcol_pre_mid (m := [Y, Z, X]) rfl hc hi (show (1:ℕ) < 3 by norm_num) hci hg1
          simp only [List.getElem_cons_zero, List.getElem_cons_succ] at this
          simpa using hYZ.trans_lt this
        · obtain rfl : x = g := by simpa using hwc.symm
          have := dcol_pre_mid (m := [Y, Z, X]) rfl hc hi (show (1:ℕ) < 3 by norm_num) hci hg1
          simp only [List.getElem_cons_zero, List.getElem_cons_succ] at this
          simpa using (hXY.trans_le hYZ).trans this
        · simp at hwc
      · intro j i x hj hi hwc hcs
        rw [Option.map_id] at hcs
        interval_cases j
        · obtain rfl : x = g := by simpa using hwc.symm
          have := dcol_mid_suf (m := [Y, Z, X]) rfl hc (show (2:ℕ) < 3 by norm_num) hi hg2 hcs
          simp only [List.getElem_cons_zero, List.getElem_cons_succ] at this
          simpa using this.trans hXY
        · obtain rfl : x = g := by simpa using hwc.symm
          simpa using dcol_mid_suf (m := [Y, Z, X]) rfl hc (show (2:ℕ) < 3 by norm_num) hi hg2 hcs
        · simp at hwc
      · intro i j x hi hj hci hcs
        rw [Option.map_id] at hcs
        exact dcol_pre_suf (m := [Y, Z, X]) rfl hc hi hj hci hcs
      · simp only [card_filter_range3, hg1, hg2, hc0]
        norm_num
    | some h =>
      -- all three letters are coloured: `Z` takes the colour of `X`, and `h` takes `Y` and `X`
      have hgh : g ≠ h := by
        rintro rfl
        have := dcol_mid_mid (m := [Y, Z, X]) rfl hc (i := 0) (j := 1) (by norm_num)
          (by norm_num) hc0 hg1
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at this
        exact absurd this (not_lt.2 hYZ)
      refine greeneSize_le_greeneCol_mix (mv := [Y, X, Z]) (τ := swapNat g h)
        (wc := fun j => if j = 2 then some g else some h) rfl rfl hc (swapNat_injective g h)
        (fun x hx => swapNat_lt (hc.lt_of_colour hg1) (hc.lt_of_colour hc0) hx) ?_ ?_ ?_ ?_ ?_ ?_
      · intro j x _ hwc
        split_ifs at hwc
        · obtain rfl : x = g := by simpa using hwc.symm
          exact hc.lt_of_colour hg1
        · obtain rfl : x = h := by simpa using hwc.symm
          exact hc.lt_of_colour hc0
      · intro i j x hij hj h1 h2
        interval_cases j
        · exact absurd hij (Nat.not_lt_zero i)
        · interval_cases i
          · simpa using hXY
        · interval_cases i
          · simp only [ite_eq_right (by norm_num : ¬(0:ℕ) = 2)] at h1 h2
            exact absurd ((Option.some.inj h2).trans (Option.some.inj h1).symm) hgh
          · simp only [ite_eq_right (by norm_num : ¬(1:ℕ) = 2)] at h1 h2
            exact absurd ((Option.some.inj h2).trans (Option.some.inj h1).symm) hgh
      · intro i j x hi hj hci hwc
        interval_cases j
        · obtain rfl : x = h := by simpa using hwc.symm
          simpa using dcol_pre_mid (m := [Y, Z, X]) rfl hc hi (show (0:ℕ) < 3 by norm_num)
            hci hc0
        · obtain rfl : x = h := by simpa using hwc.symm
          have := dcol_pre_mid (m := [Y, Z, X]) rfl hc hi (show (0:ℕ) < 3 by norm_num) hci hc0
          simp only [List.getElem_cons_zero] at this
          simpa using hXY.trans this
        · obtain rfl : x = g := by simpa using hwc.symm
          simpa using dcol_pre_mid (m := [Y, Z, X]) rfl hc hi (show (1:ℕ) < 3 by norm_num)
            hci hg1
      · intro j i x hj hi hwc hcs
        have hcs2 := map_swapNat_eq_some hcs
        interval_cases j
        · obtain rfl : x = h := by simpa using hwc.symm
          rw [swapNat_right] at hcs2
          have := dcol_mid_suf (m := [Y, Z, X]) rfl hc (show (2:ℕ) < 3 by norm_num) hi hg2 hcs2
          simp only [List.getElem_cons_zero, List.getElem_cons_succ] at this
          simpa using this.trans hXY
        · obtain rfl : x = h := by simpa using hwc.symm
          rw [swapNat_right] at hcs2
          simpa using dcol_mid_suf (m := [Y, Z, X]) rfl hc (show (2:ℕ) < 3 by norm_num) hi hg2
            hcs2
        · obtain rfl : x = g := by simpa using hwc.symm
          rw [swapNat_left] at hcs2
          have := dcol_mid_suf (m := [Y, Z, X]) rfl hc (show (0:ℕ) < 3 by norm_num) hi hc0 hcs2
          simp only [List.getElem_cons_zero] at this
          simpa using this.trans_le hYZ
      · intro i j x hi hj hci hcs
        have hcs2 := map_swapNat_eq_some hcs
        by_cases hxg : x = g
        · subst hxg
          rw [swapNat_left] at hcs2
          have h1 := dcol_pre_mid (m := [Y, Z, X]) rfl hc hi (show (1:ℕ) < 3 by norm_num) hci hg1
          have h2 := dcol_mid_suf (m := [Y, Z, X]) rfl hc (show (0:ℕ) < 3 by norm_num) hj hc0 hcs2
          simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h1 h2
          exact h2.trans_le (hYZ.trans h1.le)
        · by_cases hxh : x = h
          · subst hxh
            rw [swapNat_right] at hcs2
            have h1 := dcol_pre_mid (m := [Y, Z, X]) rfl hc hi (show (0:ℕ) < 3 by norm_num) hci hc0
            have h2 := dcol_mid_suf (m := [Y, Z, X]) rfl hc (show (2:ℕ) < 3 by norm_num) hj hg2 hcs2
            simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h1 h2
            exact h2.trans (hXY.trans h1)
          · rw [swapNat_of_ne hxg hxh] at hcs2
            exact dcol_pre_suf (m := [Y, Z, X]) rfl hc hi hj hci hcs2
      · simp only [card_filter_range3, hg1, hg2, hc0]
        norm_num
  · -- the last two letters do not share a colour : the letters keep their colours
    refine greeneSize_le_greeneCol_mix (mv := [Y, X, Z]) (τ := id)
      (wc := fun j => if j = 0 then c (p.length + 0) else if j = 1 then c (p.length + 2)
        else c (p.length + 1)) rfl rfl hc Function.injective_id (fun _ h => h) ?_ ?_ ?_ ?_ ?_ ?_
    · intro j x _ hwc
      split_ifs at hwc <;> exact hc.lt_of_colour hwc
    · intro i j x hij hj h1 h2
      interval_cases j
      · exact absurd hij (Nat.not_lt_zero i)
      · interval_cases i
        · rw [ite_eq_left rfl] at h1
          rw [ite_eq_right (by norm_num), ite_eq_left rfl] at h2
          have := dcol_mid_mid (m := [Y, Z, X]) rfl hc (i := 0) (j := 2) (by norm_num)
            (by norm_num) h1 h2
          simpa using this
      · interval_cases i
        · rw [ite_eq_left rfl] at h1
          rw [ite_eq_right (by norm_num), ite_eq_right (by norm_num)] at h2
          have := dcol_mid_mid (m := [Y, Z, X]) rfl hc (i := 0) (j := 1) (by norm_num)
            (by norm_num) h1 h2
          simpa using this
        · rw [ite_eq_right (by norm_num), ite_eq_left rfl] at h1
          rw [ite_eq_right (by norm_num), ite_eq_right (by norm_num)] at h2
          exact absurd ⟨x, h2, h1⟩ hgen
    · intro i j x hi hj hci hwc
      interval_cases j
      · rw [ite_eq_left rfl] at hwc
        simpa using dcol_pre_mid (m := [Y, Z, X]) rfl hc hi (show (0:ℕ) < 3 by norm_num) hci hwc
      · rw [ite_eq_right (by norm_num), ite_eq_left rfl] at hwc
        simpa using dcol_pre_mid (m := [Y, Z, X]) rfl hc hi (show (2:ℕ) < 3 by norm_num) hci hwc
      · rw [ite_eq_right (by norm_num), ite_eq_right (by norm_num)] at hwc
        simpa using dcol_pre_mid (m := [Y, Z, X]) rfl hc hi (show (1:ℕ) < 3 by norm_num) hci hwc
    · intro j i x hj hi hwc hcs
      rw [Option.map_id] at hcs
      interval_cases j
      · rw [ite_eq_left rfl] at hwc
        simpa using dcol_mid_suf (m := [Y, Z, X]) rfl hc (show (0:ℕ) < 3 by norm_num) hi hwc hcs
      · rw [ite_eq_right (by norm_num), ite_eq_left rfl] at hwc
        simpa using dcol_mid_suf (m := [Y, Z, X]) rfl hc (show (2:ℕ) < 3 by norm_num) hi hwc hcs
      · rw [ite_eq_right (by norm_num), ite_eq_right (by norm_num)] at hwc
        simpa using dcol_mid_suf (m := [Y, Z, X]) rfl hc (show (1:ℕ) < 3 by norm_num) hi hwc hcs
    · intro i j x hi hj hci hcs
      rw [Option.map_id] at hcs
      exact dcol_pre_suf (m := [Y, Z, X]) rfl hc hi hj hci hcs
    · simp only [card_filter_range3]
      norm_num
      split_ifs <;> omega

/-! ### Invariance under Knuth equivalence -/

theorem greeneCol_placticStep {u v : List T} (h : PlacticStep u v) (k : ℕ) :
    greeneCol u k = greeneCol v k := by
  induction h with
  | knuthAC hxy hyz a b =>
    refine le_antisymm ?_ ?_
    · simpa using greeneCol_knuthAC_le (k := k) a b hxy hyz
    · simpa using greeneCol_knuthAC_ge (k := k) a b hxy hyz
  | knuthCA hxy hyz a b =>
    refine le_antisymm ?_ ?_
    · simpa using greeneCol_knuthCA_le (k := k) a b hxy hyz
    · simpa using greeneCol_knuthCA_ge (k := k) a b hxy hyz

/-- **The Greene column invariants are plactic invariants** (Coq
`Greene_col_invar_plactic`). -/
theorem greeneCol_placticEquiv {u v : List T} (h : PlacticEquiv u v) (k : ℕ) :
    greeneCol u k = greeneCol v k := by
  induction h with
  | rel a b hab => exact greeneCol_placticStep hab k
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2

end List
