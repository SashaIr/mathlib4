/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.IntervalCases
import Mathlib.Combinatorics.Young.Greene.Defs
import Mathlib.Combinatorics.Young.Plactic.Basic

/-!
# Greene invariants are plactic invariants

A Lean 4 port of `theories/LRrule/Greene_inv.v` from
[Coq-Combi](https://github.com/math-comp/Coq-Combi) (row case).

## Main results

* `List.greeneRow_placticStep` : one Knuth move does not change the Greene invariants.
* `List.greeneRow_placticEquiv` : Knuth equivalent words have the same Greene invariants
  `greeneRow · k`.
-/

namespace List

open List

variable {T : Type*} [LinearOrder T]

/-! ### Reading letters of a word split in three pieces -/

section Split

variable (p m s : List T)

omit [LinearOrder T] in
lemma length_append_mid : (p ++ m ++ s).length = p.length + m.length + s.length := by
  simp [Nat.add_assoc]

omit [LinearOrder T] in
lemma getElem_mid_left {i : ℕ} (hi : i < p.length) :
    (p ++ m ++ s)[i]'(by simp; omega) = p[i] := by
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_left hi]

omit [LinearOrder T] in
lemma getElem_mid_mid {j : ℕ} (hj : j < m.length) :
    (p ++ m ++ s)[p.length + j]'(by simp; omega) = m[j] := by
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega)]
  simp

omit [LinearOrder T] in
lemma getElem_mid_right {i : ℕ} (hi : i < s.length) :
    (p ++ m ++ s)[p.length + m.length + i]'(by simp; omega) = s[i] := by
  rw [List.getElem_append_right (by simp)]
  congr 1
  simp

omit [LinearOrder T] in
lemma getElem_mid_left' {i : ℕ} (hi : i < p.length) (h : i < (p ++ m ++ s).length) :
    (p ++ m ++ s)[i] = p[i] := getElem_mid_left p m s hi

omit [LinearOrder T] in
lemma getElem_mid_mid' {i j : ℕ} (hj : j < m.length) (hij : i = p.length + j)
    (h : i < (p ++ m ++ s).length) : (p ++ m ++ s)[i] = m[j] := by
  subst hij; exact getElem_mid_mid p m s hj

omit [LinearOrder T] in
lemma getElem_mid_right' {i j : ℕ} (hj : j < s.length) (hij : i = p.length + m.length + j)
    (h : i < (p ++ m ++ s).length) : (p ++ m ++ s)[i] = s[j] := by
  subst hij; exact getElem_mid_right p m s hj

end Split

/-! ### Splitting the size of a colouring -/

omit [LinearOrder T] in
lemma greeneSize_split (w : List T) (c : ℕ → Option ℕ) (n l m : ℕ)
    (h : w.length = n + l + m) :
    greeneSize w c =
      ((Finset.range n).filter fun i => (c i).isSome).card +
        ((Finset.range l).filter fun j => (c (n + j)).isSome).card +
        ((Finset.range m).filter fun i => (c (n + l + i)).isSome).card := by
  simp only [greeneSize, Finset.card_filter, h]
  rw [Finset.sum_range_add, Finset.sum_range_add]

/-! ### Transferring a colouring along a change of the three middle letters -/

/-- The colouring of `p ++ mv ++ s` built from a colouring `c` of `p ++ mu ++ s`: it is
unchanged on `p`, given by `wc` on the three middle positions, and composed with the
permutation `τ` of the colours on `s`. -/
def mixCol (n : ℕ) (c wc : ℕ → Option ℕ) (τ : ℕ → ℕ) : ℕ → Option ℕ := fun i =>
  if i < n then c i else if i < n + 3 then wc (i - n) else (c i).map τ

lemma mixCol_lt {n : ℕ} {c wc : ℕ → Option ℕ} {τ : ℕ → ℕ} {i : ℕ} (hi : i < n) :
    mixCol n c wc τ i = c i := by simp [mixCol, hi]

lemma mixCol_mid {n : ℕ} {c wc : ℕ → Option ℕ} {τ : ℕ → ℕ} {j : ℕ} (hj : j < 3) :
    mixCol n c wc τ (n + j) = wc j := by
  simp only [mixCol]
  rw [if_neg (by omega), if_pos (by omega)]
  simp

lemma mixCol_gt {n : ℕ} {c wc : ℕ → Option ℕ} {τ : ℕ → ℕ} {i : ℕ} (hi : n + 3 ≤ i) :
    mixCol n c wc τ i = (c i).map τ := by
  simp only [mixCol]
  rw [if_neg (by omega), if_neg (by omega)]

/-- The key transfer lemma: a colouring of `p ++ mu ++ s` yields a colouring of
`p ++ mv ++ s`, provided the four families of comparisons hold. -/
lemma isGreeneCol_mixCol {k : ℕ} {p s mu mv : List T} {c wc : ℕ → Option ℕ} {τ : ℕ → ℕ}
    (hmu : mu.length = 3) (hmv : mv.length = 3)
    (hc : IsGreeneCol (p ++ mu ++ s) k c)
    (hτinj : Function.Injective τ) (hτk : ∀ x, x < k → τ x < k)
    (hwck : ∀ j x, j < 3 → wc j = some x → x < k)
    (h11 : ∀ i j x (hij : i < j) (hj : j < 3), wc i = some x → wc j = some x →
      mv[i]'(by omega) ≤ mv[j]'(by omega))
    (h12 : ∀ i j x (hi : i < p.length) (hj : j < 3), c i = some x → wc j = some x →
      p[i] ≤ mv[j]'(by omega))
    (h23 : ∀ j i x (hj : j < 3) (hi : i < s.length), wc j = some x →
      (c (p.length + 3 + i)).map τ = some x → mv[j]'(by omega) ≤ s[i])
    (h13 : ∀ i j x (hi : i < p.length) (hj : j < s.length), c i = some x →
      (c (p.length + 3 + j)).map τ = some x → p[i] ≤ s[j]) :
    IsGreeneCol (p ++ mv ++ s) k (mixCol p.length c wc τ) := by
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
        have := hc.le_of_colour hij (show j < (p ++ mu ++ s).length by omega) hci hcj
        exact hvi.le.trans ((hui.ge.trans (this.trans huj.le)).trans hvj.ge)
      · by_cases hj3 : j < p.length + 3
        · have hjeq : j = p.length + (j - p.length) := by omega
          have hcj' : wc (j - p.length) = some x := by
            rw [hjeq, mixCol_mid (by omega)] at hcj; exact hcj
          have hvj : (p ++ mv ++ s)[j]'hj = mv[j - p.length]'(by omega) :=
            getElem_mid_mid' p mv s (by omega) hjeq _
          exact hvi.le.trans
            ((h12 i (j - p.length) x hi (by omega) hci hcj').trans hvj.ge)
        · have hjeq : j = p.length + 3 + (j - p.length - 3) := by omega
          have hcj' : (c (p.length + 3 + (j - p.length - 3))).map τ = some x := by
            rw [mixCol_gt (by omega : p.length + 3 ≤ j)] at hcj
            rw [← hjeq]; exact hcj
          have hvj : (p ++ mv ++ s)[j]'hj = s[j - p.length - 3]'(by omega) :=
            getElem_mid_right' p mv s (by omega) (by omega) _
          exact hvi.le.trans
            ((h13 i (j - p.length - 3) x hi (by omega) hci hcj').trans hvj.ge)
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
          exact hvi.le.trans
            ((h11 (i - p.length) (j - p.length) x (by omega) (by omega) hci' hcj').trans hvj.ge)
        · have hjeq : j = p.length + 3 + (j - p.length - 3) := by omega
          have hcj' : (c (p.length + 3 + (j - p.length - 3))).map τ = some x := by
            rw [mixCol_gt (by omega : p.length + 3 ≤ j)] at hcj
            rw [← hjeq]; exact hcj
          have hvj : (p ++ mv ++ s)[j]'hj = s[j - p.length - 3]'(by omega) :=
            getElem_mid_right' p mv s (by omega) (by omega) _
          exact hvi.le.trans
            ((h23 (i - p.length) (j - p.length - 3) x (by omega) (by omega) hci' hcj').trans
              hvj.ge)
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
        have := hc.le_of_colour hij (show j < (p ++ mu ++ s).length by omega) hy hy'
        exact hvi.le.trans ((hui.ge.trans (this.trans huj.le)).trans hvj.ge)

omit [LinearOrder T] in
/-- The size of a transferred colouring. -/
lemma greeneSize_mixCol {p s mu mv : List T} {c wc : ℕ → Option ℕ} {τ : ℕ → ℕ}
    (hmu : mu.length = 3) (hmv : mv.length = 3)
    (hcount : ((Finset.range 3).filter fun j => (wc j).isSome).card =
      ((Finset.range 3).filter fun j => (c (p.length + j)).isSome).card) :
    greeneSize (p ++ mv ++ s) (mixCol p.length c wc τ) = greeneSize (p ++ mu ++ s) c := by
  rw [greeneSize_split _ _ p.length 3 s.length (by rw [length_append_mid, hmv]),
    greeneSize_split _ _ p.length 3 s.length (by rw [length_append_mid, hmu])]
  congr 1
  · congr 1
    · congr 1
      exact Finset.filter_congr (by intro i hi; simp [mixCol_lt (Finset.mem_range.1 hi)])
    · rw [← hcount]
      congr 1
      exact Finset.filter_congr (by intro j hj; simp [mixCol_mid (Finset.mem_range.1 hj)])
  · congr 1
    refine Finset.filter_congr (fun i _ => ?_)
    have : mixCol p.length c wc τ (p.length + 3 + i) = (c (p.length + 3 + i)).map τ :=
      mixCol_gt (by omega)
    simp [this]


/-! ### The comparisons satisfied by a colouring of a word split in three -/

section Facts

variable {k : ℕ} {p s m : List T} {c : ℕ → Option ℕ}

lemma col_pre_mid (hm : m.length = 3) (hc : IsGreeneCol (p ++ m ++ s) k c)
    {i j x : ℕ} (hi : i < p.length) (hj : j < 3) (hci : c i = some x)
    (hcj : c (p.length + j) = some x) : p[i] ≤ m[j]'(by omega) := by
  have hlen : (p ++ m ++ s).length = p.length + 3 + s.length := by rw [length_append_mid, hm]
  have hui : (p ++ m ++ s)[i]'(by omega) = p[i] := getElem_mid_left' p m s hi _
  have huj : (p ++ m ++ s)[p.length + j]'(by omega) = m[j]'(by omega) :=
    getElem_mid_mid' p m s (by omega) rfl _
  have := hc.le_of_colour (show i < p.length + j by omega)
    (show p.length + j < (p ++ m ++ s).length by omega) hci hcj
  exact hui.ge.trans (this.trans huj.le)

lemma col_mid_mid (hm : m.length = 3) (hc : IsGreeneCol (p ++ m ++ s) k c)
    {i j x : ℕ} (hij : i < j) (hj : j < 3) (hci : c (p.length + i) = some x)
    (hcj : c (p.length + j) = some x) : m[i]'(by omega) ≤ m[j]'(by omega) := by
  have hlen : (p ++ m ++ s).length = p.length + 3 + s.length := by rw [length_append_mid, hm]
  have hui : (p ++ m ++ s)[p.length + i]'(by omega) = m[i]'(by omega) :=
    getElem_mid_mid' p m s (by omega) rfl _
  have huj : (p ++ m ++ s)[p.length + j]'(by omega) = m[j]'(by omega) :=
    getElem_mid_mid' p m s (by omega) rfl _
  have := hc.le_of_colour (show p.length + i < p.length + j by omega)
    (show p.length + j < (p ++ m ++ s).length by omega) hci hcj
  exact hui.ge.trans (this.trans huj.le)

lemma col_mid_suf (hm : m.length = 3) (hc : IsGreeneCol (p ++ m ++ s) k c)
    {j i x : ℕ} (hj : j < 3) (hi : i < s.length) (hcj : c (p.length + j) = some x)
    (hci : c (p.length + 3 + i) = some x) : m[j]'(by omega) ≤ s[i] := by
  have hlen : (p ++ m ++ s).length = p.length + 3 + s.length := by rw [length_append_mid, hm]
  have huj : (p ++ m ++ s)[p.length + j]'(by omega) = m[j]'(by omega) :=
    getElem_mid_mid' p m s (by omega) rfl _
  have hui : (p ++ m ++ s)[p.length + 3 + i]'(by omega) = s[i] :=
    getElem_mid_right' p m s hi (by omega) _
  have := hc.le_of_colour (show p.length + j < p.length + 3 + i by omega)
    (show p.length + 3 + i < (p ++ m ++ s).length by omega) hcj hci
  exact huj.ge.trans (this.trans hui.le)

lemma col_pre_suf (hm : m.length = 3) (hc : IsGreeneCol (p ++ m ++ s) k c)
    {i j x : ℕ} (hi : i < p.length) (hj : j < s.length) (hci : c i = some x)
    (hcj : c (p.length + 3 + j) = some x) : p[i] ≤ s[j] := by
  have hlen : (p ++ m ++ s).length = p.length + 3 + s.length := by rw [length_append_mid, hm]
  have hui : (p ++ m ++ s)[i]'(by omega) = p[i] := getElem_mid_left' p m s hi _
  have huj : (p ++ m ++ s)[p.length + 3 + j]'(by omega) = s[j] :=
    getElem_mid_right' p m s hj (by omega) _
  have := hc.le_of_colour (show i < p.length + 3 + j by omega)
    (show p.length + 3 + j < (p ++ m ++ s).length by omega) hci hcj
  exact hui.ge.trans (this.trans huj.le)

end Facts

/-- Combination of `isGreeneCol_mixCol` and `greeneSize_mixCol`. -/
lemma greeneSize_le_greeneRow_mix {k : ℕ} {p s mu mv : List T} {c wc : ℕ → Option ℕ} {τ : ℕ → ℕ}
    (hmu : mu.length = 3) (hmv : mv.length = 3)
    (hc : IsGreeneCol (p ++ mu ++ s) k c)
    (hτinj : Function.Injective τ) (hτk : ∀ x, x < k → τ x < k)
    (hwck : ∀ j x, j < 3 → wc j = some x → x < k)
    (h11 : ∀ i j x (hij : i < j) (hj : j < 3), wc i = some x → wc j = some x →
      mv[i]'(by omega) ≤ mv[j]'(by omega))
    (h12 : ∀ i j x (hi : i < p.length) (hj : j < 3), c i = some x → wc j = some x →
      p[i] ≤ mv[j]'(by omega))
    (h23 : ∀ j i x (hj : j < 3) (hi : i < s.length), wc j = some x →
      (c (p.length + 3 + i)).map τ = some x → mv[j]'(by omega) ≤ s[i])
    (h13 : ∀ i j x (hi : i < p.length) (hj : j < s.length), c i = some x →
      (c (p.length + 3 + j)).map τ = some x → p[i] ≤ s[j])
    (hcount : ((Finset.range 3).filter fun j => (wc j).isSome).card =
      ((Finset.range 3).filter fun j => (c (p.length + j)).isSome).card) :
    greeneSize (p ++ mu ++ s) c ≤ greeneRow (p ++ mv ++ s) k := by
  rw [← greeneSize_mixCol (mu := mu) (mv := mv) (τ := τ) hmu hmv hcount]
  exact le_greeneRow (isGreeneCol_mixCol hmu hmv hc hτinj hτk hwck h11 h12 h23 h13)

lemma card_filter_range3 (f : ℕ → Option ℕ) :
    ((Finset.range 3).filter fun j => (f j).isSome).card =
      (if (f 0).isSome then 1 else 0) + (if (f 1).isSome then 1 else 0) +
        (if (f 2).isSome then 1 else 0) := by
  rw [Finset.card_filter, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]

/-! ### The four elementary Knuth moves -/

/-- The easy direction of the first Knuth relation: the three letters keep their colours. -/
lemma greeneRow_knuthAC_ge {k : ℕ} (p s : List T) {X Y Z : T} (hXY : X ≤ Y) (hYZ : Y < Z) :
    greeneRow (p ++ [Z, X, Y] ++ s) k ≤ greeneRow (p ++ [X, Z, Y] ++ s) k := by
  refine greeneRow_le fun c hc => ?_
  refine greeneSize_le_greeneRow_mix (mv := [X, Z, Y]) (τ := id)
    (wc := fun j => if j = 0 then c (p.length + 1) else if j = 1 then c (p.length + 0)
      else c (p.length + 2)) rfl rfl hc Function.injective_id (fun _ h => h) ?_ ?_ ?_ ?_ ?_ ?_
  · intro j x _ hwc
    simp only at hwc
    split_ifs at hwc <;> exact hc.lt_of_colour hwc
  · intro i j x hij hj h1 h2
    simp only at h1 h2
    interval_cases j
    · exact absurd hij (Nat.not_lt_zero i)
    · interval_cases i
      · rw [if_pos rfl] at h1
        rw [if_neg (by norm_num), if_pos rfl] at h2
        have := col_mid_mid (m := [Z, X, Y]) rfl hc (i := 0) (j := 1) (by norm_num)
          (by norm_num) h2 h1
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at this
        exact absurd this (not_le.2 (lt_of_le_of_lt hXY hYZ))
    · interval_cases i
      · rw [if_pos rfl] at h1
        rw [if_neg (by norm_num), if_neg (by norm_num)] at h2
        have := col_mid_mid (m := [Z, X, Y]) rfl hc (i := 1) (j := 2) (by norm_num)
          (by norm_num) h1 h2
        simpa using this
      · rw [if_neg (by norm_num), if_pos rfl] at h1
        rw [if_neg (by norm_num), if_neg (by norm_num)] at h2
        have := col_mid_mid (m := [Z, X, Y]) rfl hc (i := 0) (j := 2) (by norm_num)
          (by norm_num) h1 h2
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at this
        exact absurd this (not_le.2 hYZ)
  · intro i j x hi hj hci hwc
    simp only at hwc
    interval_cases j
    · rw [if_pos rfl] at hwc
      have := col_pre_mid (m := [Z, X, Y]) rfl hc hi (show (1:ℕ) < 3 by norm_num) hci hwc
      simpa using this
    · rw [if_neg (by norm_num), if_pos rfl] at hwc
      have := col_pre_mid (m := [Z, X, Y]) rfl hc hi (show (0:ℕ) < 3 by norm_num) hci hwc
      simpa using this
    · rw [if_neg (by norm_num), if_neg (by norm_num)] at hwc
      have := col_pre_mid (m := [Z, X, Y]) rfl hc hi (show (2:ℕ) < 3 by norm_num) hci hwc
      simpa using this
  · intro j i x hj hi hwc hcs
    rw [Option.map_id] at hcs
    simp only at hwc
    interval_cases j
    · rw [if_pos rfl] at hwc
      have := col_mid_suf (m := [Z, X, Y]) rfl hc (show (1:ℕ) < 3 by norm_num) hi hwc hcs
      simpa using this
    · rw [if_neg (by norm_num), if_pos rfl] at hwc
      have := col_mid_suf (m := [Z, X, Y]) rfl hc (show (0:ℕ) < 3 by norm_num) hi hwc hcs
      simpa using this
    · rw [if_neg (by norm_num), if_neg (by norm_num)] at hwc
      have := col_mid_suf (m := [Z, X, Y]) rfl hc (show (2:ℕ) < 3 by norm_num) hi hwc hcs
      simpa using this
  · intro i j x hi hj hci hcs
    rw [Option.map_id] at hcs
    exact col_pre_suf (m := [Z, X, Y]) rfl hc hi hj hci hcs
  · simp only [card_filter_range3]
    norm_num
    split_ifs <;> omega

/-- The easy direction of the second Knuth relation: the three letters keep their colours. -/
lemma greeneRow_knuthCA_ge {k : ℕ} (p s : List T) {X Y Z : T} (hXY : X < Y) (hYZ : Y ≤ Z) :
    greeneRow (p ++ [Y, Z, X] ++ s) k ≤ greeneRow (p ++ [Y, X, Z] ++ s) k := by
  refine greeneRow_le fun c hc => ?_
  refine greeneSize_le_greeneRow_mix (mv := [Y, X, Z]) (τ := id)
    (wc := fun j => if j = 0 then c (p.length + 0) else if j = 1 then c (p.length + 2)
      else c (p.length + 1)) rfl rfl hc Function.injective_id (fun _ h => h) ?_ ?_ ?_ ?_ ?_ ?_
  · intro j x _ hwc
    simp only at hwc
    split_ifs at hwc <;> exact hc.lt_of_colour hwc
  · intro i j x hij hj h1 h2
    simp only at h1 h2
    interval_cases j
    · exact absurd hij (Nat.not_lt_zero i)
    · interval_cases i
      · rw [if_pos rfl] at h1
        rw [if_neg (by norm_num), if_pos rfl] at h2
        have := col_mid_mid rfl hc (i := 0) (j := 2) (by norm_num) (by norm_num) h1 h2
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at this
        exact absurd this (not_le.2 hXY)
    · interval_cases i
      · rw [if_pos rfl] at h1
        rw [if_neg (by norm_num), if_neg (by norm_num)] at h2
        have := col_mid_mid rfl hc (i := 0) (j := 1) (by norm_num) (by norm_num) h1 h2
        simpa using this
      · rw [if_neg (by norm_num), if_pos rfl] at h1
        rw [if_neg (by norm_num), if_neg (by norm_num)] at h2
        have := col_mid_mid rfl hc (i := 1) (j := 2) (by norm_num) (by norm_num) h2 h1
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at this
        exact absurd this (not_le.2 (lt_of_lt_of_le hXY hYZ))
  · intro i j x hi hj hci hwc
    simp only at hwc
    interval_cases j
    · rw [if_pos rfl] at hwc
      simpa using col_pre_mid rfl hc hi (show (0:ℕ) < 3 by norm_num) hci hwc
    · rw [if_neg (by norm_num), if_pos rfl] at hwc
      simpa using col_pre_mid rfl hc hi (show (2:ℕ) < 3 by norm_num) hci hwc
    · rw [if_neg (by norm_num), if_neg (by norm_num)] at hwc
      simpa using col_pre_mid rfl hc hi (show (1:ℕ) < 3 by norm_num) hci hwc
  · intro j i x hj hi hwc hcs
    rw [Option.map_id] at hcs
    simp only at hwc
    interval_cases j
    · rw [if_pos rfl] at hwc
      simpa using col_mid_suf rfl hc (show (0:ℕ) < 3 by norm_num) hi hwc hcs
    · rw [if_neg (by norm_num), if_pos rfl] at hwc
      simpa using col_mid_suf rfl hc (show (2:ℕ) < 3 by norm_num) hi hwc hcs
    · rw [if_neg (by norm_num), if_neg (by norm_num)] at hwc
      simpa using col_mid_suf rfl hc (show (1:ℕ) < 3 by norm_num) hi hwc hcs
  · intro i j x hi hj hci hcs
    rw [Option.map_id] at hcs
    exact col_pre_suf rfl hc hi hj hci hcs
  · simp only [card_filter_range3]
    norm_num
    split_ifs <;> omega

/-! ### Exchanging two colours -/

/-- The transposition of the two colours `g` and `h`. -/
def swapNat (g h t : ℕ) : ℕ := if t = g then h else if t = h then g else t

lemma swapNat_left (g h : ℕ) : swapNat g h g = h := by simp [swapNat]

lemma swapNat_right (g h : ℕ) : swapNat g h h = g := by
  unfold swapNat; split_ifs with h1 <;> simp_all

lemma swapNat_of_ne {g h t : ℕ} (h1 : t ≠ g) (h2 : t ≠ h) : swapNat g h t = t := by
  simp [swapNat, h1, h2]

lemma swapNat_involutive (g h : ℕ) : Function.Involutive (swapNat g h) := by
  intro t
  by_cases h1 : t = g
  · subst h1; rw [swapNat_left, swapNat_right]
  · by_cases h2 : t = h
    · subst h2; rw [swapNat_right, swapNat_left]
    · rw [swapNat_of_ne h1 h2, swapNat_of_ne h1 h2]

lemma swapNat_injective (g h : ℕ) : Function.Injective (swapNat g h) :=
  (swapNat_involutive g h).injective

lemma swapNat_lt {g h k : ℕ} (hg : g < k) (hh : h < k) {t : ℕ} (ht : t < k) :
    swapNat g h t < k := by
  unfold swapNat; split_ifs <;> assumption

lemma map_swapNat_eq_some {g h : ℕ} {o : Option ℕ} {x : ℕ}
    (H : o.map (swapNat g h) = some x) : o = some (swapNat g h x) := by
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 H
  rw [swapNat_involutive g h t, ht]

/-! ### The first Knuth relation -/

/-- The hard direction of the first Knuth relation. -/
lemma greeneRow_knuthAC_le {k : ℕ} (p s : List T) {X Y Z : T} (hXY : X ≤ Y) (hYZ : Y < Z) :
    greeneRow (p ++ [X, Z, Y] ++ s) k ≤ greeneRow (p ++ [Z, X, Y] ++ s) k := by
  refine greeneRow_le fun c hc => ?_
  by_cases hgen : ∃ g, c (p.length + 0) = some g ∧ c (p.length + 1) = some g
  · obtain ⟨g, hg0, hg1⟩ := hgen
    cases hc2 : c (p.length + 2) with
    | none =>
      -- the third letter is not coloured: `Z` is dropped and `g` takes `X` and `Y`
      refine greeneSize_le_greeneRow_mix (mv := [Z, X, Y]) (τ := id)
        (wc := fun j => if j = 0 then none else some g) rfl rfl hc Function.injective_id
        (fun _ h => h) ?_ ?_ ?_ ?_ ?_ ?_
      · intro j x _ hwc
        simp only at hwc
        split_ifs at hwc
        obtain rfl : x = g := by simpa using hwc.symm
        exact hc.lt_of_colour hg0
      · intro i j x hij hj h1 h2
        simp only at h1 h2
        interval_cases j
        · exact absurd hij (Nat.not_lt_zero i)
        · interval_cases i
          · simp at h1
        · interval_cases i
          · simp at h1
          · simpa using hXY
      · intro i j x hi hj hci hwc
        simp only at hwc
        interval_cases j
        · simp at hwc
        · obtain rfl : x = g := by simpa using hwc.symm
          simpa using col_pre_mid rfl hc hi (show (0:ℕ) < 3 by norm_num) hci hg0
        · obtain rfl : x = g := by simpa using hwc.symm
          have := col_pre_mid rfl hc hi (show (0:ℕ) < 3 by norm_num) hci hg0
          simp only [List.getElem_cons_zero] at this
          simpa using this.trans hXY
      · intro j i x hj hi hwc hcs
        rw [Option.map_id] at hcs
        simp only at hwc
        interval_cases j
        · simp at hwc
        · obtain rfl : x = g := by simpa using hwc.symm
          have := col_mid_suf rfl hc (show (1:ℕ) < 3 by norm_num) hi hg1 hcs
          simpa using (hXY.trans hYZ.le).trans this
        · obtain rfl : x = g := by simpa using hwc.symm
          have := col_mid_suf rfl hc (show (1:ℕ) < 3 by norm_num) hi hg1 hcs
          simpa using hYZ.le.trans this
      · intro i j x hi hj hci hcs
        rw [Option.map_id] at hcs
        exact col_pre_suf rfl hc hi hj hci hcs
      · simp only [card_filter_range3, hg0, hg1, hc2]
        norm_num
    | some h =>
      -- all three letters are coloured: `Z` takes the colour of `Y`, and `g` takes `X` and `Y`
      have hgh : g ≠ h := by
        rintro rfl
        have := col_mid_mid rfl hc (i := 1) (j := 2) (by norm_num) (by norm_num) hg1 hc2
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at this
        exact absurd this (not_le.2 hYZ)
      refine greeneSize_le_greeneRow_mix (mv := [Z, X, Y]) (τ := swapNat g h)
        (wc := fun j => if j = 0 then some h else some g) rfl rfl hc (swapNat_injective g h)
        (fun x hx => swapNat_lt (hc.lt_of_colour hg0) (hc.lt_of_colour hc2) hx) ?_ ?_ ?_ ?_ ?_ ?_
      · intro j x _ hwc
        simp only at hwc
        split_ifs at hwc
        · obtain rfl : x = h := by simpa using hwc.symm
          exact hc.lt_of_colour hc2
        · obtain rfl : x = g := by simpa using hwc.symm
          exact hc.lt_of_colour hg0
      · intro i j x hij hj h1 h2
        simp only at h1 h2
        interval_cases j
        · exact absurd hij (Nat.not_lt_zero i)
        · interval_cases i
          · simp only [if_neg (by norm_num : ¬(1:ℕ) = 0)] at h1 h2
            exact absurd ((Option.some.inj h2).trans (Option.some.inj h1).symm) hgh
        · interval_cases i
          · simp only [if_neg (by norm_num : ¬(2:ℕ) = 0)] at h1 h2
            exact absurd ((Option.some.inj h2).trans (Option.some.inj h1).symm) hgh
          · simpa using hXY
      · intro i j x hi hj hci hwc
        simp only at hwc
        interval_cases j
        · obtain rfl : x = h := by simpa using hwc.symm
          have := col_pre_mid rfl hc hi (show (2:ℕ) < 3 by norm_num) hci hc2
          simpa using this.trans hYZ.le
        · obtain rfl : x = g := by simpa using hwc.symm
          simpa using col_pre_mid rfl hc hi (show (0:ℕ) < 3 by norm_num) hci hg0
        · obtain rfl : x = g := by simpa using hwc.symm
          have := col_pre_mid rfl hc hi (show (0:ℕ) < 3 by norm_num) hci hg0
          simp only [List.getElem_cons_zero] at this
          simpa using this.trans hXY
      · intro j i x hj hi hwc hcs
        have hcs2 := map_swapNat_eq_some hcs
        simp only at hwc
        interval_cases j
        · obtain rfl : x = h := by simpa using hwc.symm
          rw [swapNat_right] at hcs2
          simpa using col_mid_suf rfl hc (show (1:ℕ) < 3 by norm_num) hi hg1 hcs2
        · obtain rfl : x = g := by simpa using hwc.symm
          rw [swapNat_left] at hcs2
          have := col_mid_suf rfl hc (show (2:ℕ) < 3 by norm_num) hi hc2 hcs2
          simpa using hXY.trans this
        · obtain rfl : x = g := by simpa using hwc.symm
          rw [swapNat_left] at hcs2
          simpa using col_mid_suf rfl hc (show (2:ℕ) < 3 by norm_num) hi hc2 hcs2
      · intro i j x hi hj hci hcs
        have hcs2 := map_swapNat_eq_some hcs
        by_cases hxg : x = g
        · subst hxg
          rw [swapNat_left] at hcs2
          have h1 := col_pre_mid rfl hc hi (show (0:ℕ) < 3 by norm_num) hci hg0
          have h2 := col_mid_suf rfl hc (show (2:ℕ) < 3 by norm_num) hj hc2 hcs2
          simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h1 h2
          exact h1.trans (hXY.trans h2)
        · by_cases hxh : x = h
          · subst hxh
            rw [swapNat_right] at hcs2
            have h1 := col_pre_mid rfl hc hi (show (2:ℕ) < 3 by norm_num) hci hc2
            have h2 := col_mid_suf rfl hc (show (1:ℕ) < 3 by norm_num) hj hg1 hcs2
            simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h1 h2
            exact h1.trans (hYZ.le.trans h2)
          · rw [swapNat_of_ne hxg hxh] at hcs2
            exact col_pre_suf rfl hc hi hj hci hcs2
      · simp only [card_filter_range3, hg0, hg1, hc2]
        norm_num
  · -- the first two letters do not share a colour : the letters keep their colours
    refine greeneSize_le_greeneRow_mix (mv := [Z, X, Y]) (τ := id)
      (wc := fun j => if j = 0 then c (p.length + 1) else if j = 1 then c (p.length + 0)
        else c (p.length + 2)) rfl rfl hc Function.injective_id (fun _ h => h) ?_ ?_ ?_ ?_ ?_ ?_
    · intro j x _ hwc
      simp only at hwc
      split_ifs at hwc <;> exact hc.lt_of_colour hwc
    · intro i j x hij hj h1 h2
      simp only at h1 h2
      interval_cases j
      · exact absurd hij (Nat.not_lt_zero i)
      · interval_cases i
        · rw [if_pos rfl] at h1
          rw [if_neg (by norm_num), if_pos rfl] at h2
          exact absurd ⟨x, h2, h1⟩ hgen
      · interval_cases i
        · rw [if_pos rfl] at h1
          rw [if_neg (by norm_num), if_neg (by norm_num)] at h2
          have := col_mid_mid rfl hc (i := 1) (j := 2) (by norm_num) (by norm_num) h1 h2
          exact absurd this (not_le.2 hYZ)
        · rw [if_neg (by norm_num), if_pos rfl] at h1
          rw [if_neg (by norm_num), if_neg (by norm_num)] at h2
          simpa using hXY
    · intro i j x hi hj hci hwc
      simp only at hwc
      interval_cases j
      · rw [if_pos rfl] at hwc
        simpa using col_pre_mid rfl hc hi (show (1:ℕ) < 3 by norm_num) hci hwc
      · rw [if_neg (by norm_num), if_pos rfl] at hwc
        simpa using col_pre_mid rfl hc hi (show (0:ℕ) < 3 by norm_num) hci hwc
      · rw [if_neg (by norm_num), if_neg (by norm_num)] at hwc
        simpa using col_pre_mid rfl hc hi (show (2:ℕ) < 3 by norm_num) hci hwc
    · intro j i x hj hi hwc hcs
      rw [Option.map_id] at hcs
      simp only at hwc
      interval_cases j
      · rw [if_pos rfl] at hwc
        simpa using col_mid_suf rfl hc (show (1:ℕ) < 3 by norm_num) hi hwc hcs
      · rw [if_neg (by norm_num), if_pos rfl] at hwc
        simpa using col_mid_suf rfl hc (show (0:ℕ) < 3 by norm_num) hi hwc hcs
      · rw [if_neg (by norm_num), if_neg (by norm_num)] at hwc
        simpa using col_mid_suf rfl hc (show (2:ℕ) < 3 by norm_num) hi hwc hcs
    · intro i j x hi hj hci hcs
      rw [Option.map_id] at hcs
      exact col_pre_suf rfl hc hi hj hci hcs
    · simp only [card_filter_range3]
      norm_num
      split_ifs <;> omega

/-! ### The second Knuth relation -/

/-- The hard direction of the second Knuth relation. -/
lemma greeneRow_knuthCA_le {k : ℕ} (p s : List T) {X Y Z : T} (hXY : X < Y) (hYZ : Y ≤ Z) :
    greeneRow (p ++ [Y, X, Z] ++ s) k ≤ greeneRow (p ++ [Y, Z, X] ++ s) k := by
  refine greeneRow_le fun c hc => ?_
  by_cases hgen : ∃ g, c (p.length + 1) = some g ∧ c (p.length + 2) = some g
  · obtain ⟨g, hg1, hg2⟩ := hgen
    cases hc0 : c (p.length + 0) with
    | none =>
      -- the first letter is not coloured: `X` is dropped and `g` takes `Y` and `Z`
      refine greeneSize_le_greeneRow_mix (mv := [Y, Z, X]) (τ := id)
        (wc := fun j => if j = 2 then none else some g) rfl rfl hc Function.injective_id
        (fun _ h => h) ?_ ?_ ?_ ?_ ?_ ?_
      · intro j x _ hwc
        simp only at hwc
        split_ifs at hwc
        obtain rfl : x = g := by simpa using hwc.symm
        exact hc.lt_of_colour hg1
      · intro i j x hij hj h1 h2
        simp only at h1 h2
        interval_cases j
        · exact absurd hij (Nat.not_lt_zero i)
        · interval_cases i
          · simpa using hYZ
        · simp at h2
      · intro i j x hi hj hci hwc
        simp only at hwc
        interval_cases j
        · obtain rfl : x = g := by simpa using hwc.symm
          have := col_pre_mid rfl hc hi (show (1:ℕ) < 3 by norm_num) hci hg1
          simpa using this.trans hXY.le
        · obtain rfl : x = g := by simpa using hwc.symm
          have := col_pre_mid rfl hc hi (show (1:ℕ) < 3 by norm_num) hci hg1
          simpa using this.trans (hXY.le.trans hYZ)
        · simp at hwc
      · intro j i x hj hi hwc hcs
        rw [Option.map_id] at hcs
        simp only at hwc
        interval_cases j
        · obtain rfl : x = g := by simpa using hwc.symm
          have := col_mid_suf rfl hc (show (2:ℕ) < 3 by norm_num) hi hg2 hcs
          simpa using hYZ.trans this
        · obtain rfl : x = g := by simpa using hwc.symm
          simpa using col_mid_suf rfl hc (show (2:ℕ) < 3 by norm_num) hi hg2 hcs
        · simp at hwc
      · intro i j x hi hj hci hcs
        rw [Option.map_id] at hcs
        exact col_pre_suf rfl hc hi hj hci hcs
      · simp only [card_filter_range3, hg1, hg2, hc0]
        norm_num
    | some h =>
      -- all three letters are coloured: `X` keeps the colour `g`, and `h` takes `Y` and `Z`
      have hgh : g ≠ h := by
        rintro rfl
        have := col_mid_mid rfl hc (i := 0) (j := 1) (by norm_num) (by norm_num) hc0 hg1
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at this
        exact absurd this (not_le.2 hXY)
      refine greeneSize_le_greeneRow_mix (mv := [Y, Z, X]) (τ := swapNat g h)
        (wc := fun j => if j = 2 then some g else some h) rfl rfl hc (swapNat_injective g h)
        (fun x hx => swapNat_lt (hc.lt_of_colour hg1) (hc.lt_of_colour hc0) hx) ?_ ?_ ?_ ?_ ?_ ?_
      · intro j x _ hwc
        simp only at hwc
        split_ifs at hwc
        · obtain rfl : x = g := by simpa using hwc.symm
          exact hc.lt_of_colour hg1
        · obtain rfl : x = h := by simpa using hwc.symm
          exact hc.lt_of_colour hc0
      · intro i j x hij hj h1 h2
        simp only at h1 h2
        interval_cases j
        · exact absurd hij (Nat.not_lt_zero i)
        · interval_cases i
          · simpa using hYZ
        · interval_cases i
          · simp only [if_neg (by norm_num : ¬(0:ℕ) = 2)] at h1 h2
            exact absurd ((Option.some.inj h2).trans (Option.some.inj h1).symm) hgh
          · simp only [if_neg (by norm_num : ¬(1:ℕ) = 2)] at h1 h2
            exact absurd ((Option.some.inj h2).trans (Option.some.inj h1).symm) hgh
      · intro i j x hi hj hci hwc
        simp only at hwc
        interval_cases j
        · obtain rfl : x = h := by simpa using hwc.symm
          simpa using col_pre_mid rfl hc hi (show (0:ℕ) < 3 by norm_num) hci hc0
        · obtain rfl : x = h := by simpa using hwc.symm
          have := col_pre_mid rfl hc hi (show (0:ℕ) < 3 by norm_num) hci hc0
          simp only [List.getElem_cons_zero] at this
          simpa using this.trans hYZ
        · obtain rfl : x = g := by simpa using hwc.symm
          simpa using col_pre_mid rfl hc hi (show (1:ℕ) < 3 by norm_num) hci hg1
      · intro j i x hj hi hwc hcs
        have hcs2 := map_swapNat_eq_some hcs
        simp only at hwc
        interval_cases j
        · obtain rfl : x = h := by simpa using hwc.symm
          rw [swapNat_right] at hcs2
          have := col_mid_suf rfl hc (show (2:ℕ) < 3 by norm_num) hi hg2 hcs2
          simpa using hYZ.trans this
        · obtain rfl : x = h := by simpa using hwc.symm
          rw [swapNat_right] at hcs2
          simpa using col_mid_suf rfl hc (show (2:ℕ) < 3 by norm_num) hi hg2 hcs2
        · obtain rfl : x = g := by simpa using hwc.symm
          rw [swapNat_left] at hcs2
          have := col_mid_suf rfl hc (show (0:ℕ) < 3 by norm_num) hi hc0 hcs2
          simpa using hXY.le.trans this
      · intro i j x hi hj hci hcs
        have hcs2 := map_swapNat_eq_some hcs
        by_cases hxg : x = g
        · subst hxg
          rw [swapNat_left] at hcs2
          have h1 := col_pre_mid rfl hc hi (show (1:ℕ) < 3 by norm_num) hci hg1
          have h2 := col_mid_suf rfl hc (show (0:ℕ) < 3 by norm_num) hj hc0 hcs2
          simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h1 h2
          exact h1.trans (hXY.le.trans h2)
        · by_cases hxh : x = h
          · subst hxh
            rw [swapNat_right] at hcs2
            have h1 := col_pre_mid rfl hc hi (show (0:ℕ) < 3 by norm_num) hci hc0
            have h2 := col_mid_suf rfl hc (show (2:ℕ) < 3 by norm_num) hj hg2 hcs2
            simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h1 h2
            exact h1.trans (hYZ.trans h2)
          · rw [swapNat_of_ne hxg hxh] at hcs2
            exact col_pre_suf rfl hc hi hj hci hcs2
      · simp only [card_filter_range3, hg1, hg2, hc0]
        norm_num
  · -- the last two letters do not share a colour: the letters keep their colours
    refine greeneSize_le_greeneRow_mix (mv := [Y, Z, X]) (τ := id)
      (wc := fun j => if j = 0 then c (p.length + 0) else if j = 1 then c (p.length + 2)
        else c (p.length + 1)) rfl rfl hc Function.injective_id (fun _ h => h) ?_ ?_ ?_ ?_ ?_ ?_
    · intro j x _ hwc
      simp only at hwc
      split_ifs at hwc <;> exact hc.lt_of_colour hwc
    · intro i j x hij hj h1 h2
      simp only at h1 h2
      interval_cases j
      · exact absurd hij (Nat.not_lt_zero i)
      · interval_cases i
        · simpa using hYZ
      · interval_cases i
        · rw [if_pos rfl] at h1
          rw [if_neg (by norm_num), if_neg (by norm_num)] at h2
          have := col_mid_mid rfl hc (i := 0) (j := 1) (by norm_num) (by norm_num) h1 h2
          exact absurd this (not_le.2 hXY)
        · rw [if_neg (by norm_num), if_pos rfl] at h1
          rw [if_neg (by norm_num), if_neg (by norm_num)] at h2
          exact absurd ⟨x, h2, h1⟩ hgen
    · intro i j x hi hj hci hwc
      simp only at hwc
      interval_cases j
      · rw [if_pos rfl] at hwc
        simpa using col_pre_mid rfl hc hi (show (0:ℕ) < 3 by norm_num) hci hwc
      · rw [if_neg (by norm_num), if_pos rfl] at hwc
        simpa using col_pre_mid rfl hc hi (show (2:ℕ) < 3 by norm_num) hci hwc
      · rw [if_neg (by norm_num), if_neg (by norm_num)] at hwc
        simpa using col_pre_mid rfl hc hi (show (1:ℕ) < 3 by norm_num) hci hwc
    · intro j i x hj hi hwc hcs
      rw [Option.map_id] at hcs
      simp only at hwc
      interval_cases j
      · rw [if_pos rfl] at hwc
        simpa using col_mid_suf rfl hc (show (0:ℕ) < 3 by norm_num) hi hwc hcs
      · rw [if_neg (by norm_num), if_pos rfl] at hwc
        simpa using col_mid_suf rfl hc (show (2:ℕ) < 3 by norm_num) hi hwc hcs
      · rw [if_neg (by norm_num), if_neg (by norm_num)] at hwc
        simpa using col_mid_suf rfl hc (show (1:ℕ) < 3 by norm_num) hi hwc hcs
    · intro i j x hi hj hci hcs
      rw [Option.map_id] at hcs
      exact col_pre_suf rfl hc hi hj hci hcs
    · simp only [card_filter_range3]
      norm_num
      split_ifs <;> omega

/-! ### Invariance under Knuth equivalence -/

/-- The Greene invariants do not change under an elementary Knuth transformation. -/
theorem greeneRow_placticStep {u v : List T} (h : PlacticStep u v) (k : ℕ) :
    greeneRow u k = greeneRow v k := by
  cases h with
  | knuthAC hxy hyz a b =>
    refine le_antisymm ?_ ?_
    · simpa using greeneRow_knuthAC_le (k := k) a b hxy hyz
    · simpa using greeneRow_knuthAC_ge (k := k) a b hxy hyz
  | knuthCA hxy hyz a b =>
    refine le_antisymm ?_ ?_
    · simpa using greeneRow_knuthCA_le (k := k) a b hxy hyz
    · simpa using greeneRow_knuthCA_ge (k := k) a b hxy hyz

/-- **The Greene invariants are plactic invariants** (Coq `Greene_row_invar_plactic`). -/
theorem greeneRow_placticEquiv {u v : List T} (h : PlacticEquiv u v) (k : ℕ) :
    greeneRow u k = greeneRow v k := by
  induction h with
  | rel a b hab => exact greeneRow_placticStep hab k
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2

end List
