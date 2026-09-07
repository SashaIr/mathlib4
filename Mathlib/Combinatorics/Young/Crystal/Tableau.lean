/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.Tableau.Skew
import Mathlib.Combinatorics.Young.Crystal.Basic

/-!
# Crystal operators on skew tableaux

The crystal operators `List.crystalE` and `List.crystalF` act on words.  This file shows
that they preserve the set of reading words of skew tableaux of a given shape: if `t` is a
skew tableau with inner shape `inner` and `crystalE i (toWord t) = some w`, then `w` is the
reading word of a skew tableau `t'` with the same inner shape and the same shape, and
similarly for `crystalF`.

The proof goes by induction on the rows, using the tensor rule `List.crystalE_append` to
decide whether the operator acts on the top row of the tableau or on the rows below it.

## Main definitions

* `List.countLt v r` : the number of entries of the list `r` which are smaller than `v`.

## Main results

* `List.IsRow.crystalE_eq` and `List.IsRow.crystalF_eq` : on a row, the crystal operators
  change the first letter `i + 1` into an `i`, resp. the last letter `i` into an `i + 1`.
* `List.exists_isSkewTableau_crystalE` and `List.exists_isSkewTableau_crystalF` : the
  crystal operators preserve reading words of skew tableaux of a given shape.
-/

namespace List

open List

/-! ### Counting the small entries of a row -/

/-- The number of entries of the list `r` which are smaller than `v`. -/
def countLt (v : ℕ) (r : List ℕ) : ℕ := r.countP (fun x => decide (x < v))

@[simp] lemma countLt_nil (v : ℕ) : countLt v [] = 0 := rfl

lemma countLt_cons (v x : ℕ) (r : List ℕ) :
    countLt v (x :: r) = if x < v then countLt v r + 1 else countLt v r := by
  rw [countLt, countLt, List.countP_cons]
  by_cases h : x < v <;> simp [h]

lemma countLt_le_length (v : ℕ) (r : List ℕ) : countLt v r ≤ r.length :=
  List.countP_le_length

lemma countLt_eq_zero_of_forall {v : ℕ} {r : List ℕ} (h : ∀ y ∈ r, v ≤ y) : countLt v r = 0 :=
  List.countP_eq_zero.2 fun a ha => by simpa using h a ha

lemma countLt_pos_of_mem {v y : ℕ} {r : List ℕ} (hy : y ∈ r) (h : y < v) : 0 < countLt v r :=
  List.countP_pos_iff.2 ⟨y, hy, by simpa using h⟩

/-- Splitting the entries smaller than `v + 1` into those smaller than `v` and those equal
to `v`. -/
lemma countLt_succ (v : ℕ) (r : List ℕ) : countLt (v + 1) r = countLt v r + r.count v := by
  induction r with
  | nil => simp
  | cons x r ih =>
    rw [countLt_cons, countLt_cons, List.count_cons, ih]
    rcases lt_trichotomy x v with h | rfl | h <;> simp only [beq_iff_eq] <;> split_ifs <;> omega

/-! ### Rows -/

lemma IsRow.le_of_mem_cons {x : ℕ} {r : List ℕ} (h : IsRow (x :: r)) {y : ℕ} (hy : y ∈ r) :
    x ≤ y := by
  obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.1 hy
  simpa using h.getElem_le (i := 0) (j := n + 1) (by omega) (by simpa using hn)

/-- In a row, the entries smaller than `v` are exactly the first `countLt v r` ones. -/
lemma IsRow.getElem_lt_iff {r : List ℕ} (h : IsRow r) {k : ℕ} (hk : k < r.length) (v : ℕ) :
    r[k] < v ↔ k < countLt v r := by
  constructor
  · intro hlt
    have h1 : countLt v (r.take (k + 1)) ≤ countLt v r := (List.take_sublist _ _).countP_le
    have h2 : countLt v (r.take (k + 1)) = (r.take (k + 1)).length := by
      refine List.countP_eq_length.2 ?_
      intro x hx
      obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.1 hx
      rw [List.length_take] at hn
      have hnr : n < r.length := by omega
      rw [List.getElem_take]
      have : r[n] ≤ r[k] := h.getElem_le (by omega) hk
      simp only [decide_eq_true_eq]; omega
    have h3 : (r.take (k + 1)).length = k + 1 := by rw [List.length_take]; omega
    omega
  · intro hlt
    by_contra hge
    push_neg at hge
    have hsplit : countLt v r = countLt v (r.take k) + countLt v (r.drop k) := by
      rw [countLt, countLt, countLt, ← List.countP_append, List.take_append_drop]
    have h0 : countLt v (r.drop k) = 0 := by
      refine List.countP_eq_zero.2 ?_
      intro x hx
      obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.1 hx
      rw [List.length_drop] at hn
      rw [List.getElem_drop]
      have : r[k] ≤ r[k + n]'(by omega) := h.getElem_le (by omega) (by omega)
      simp only [decide_eq_true_eq, not_lt]; omega
    have h4 : countLt v (r.take k) ≤ (r.take k).length := countLt_le_length _ _
    have h5 : (r.take k).length ≤ k := by rw [List.length_take]; omega
    omega

/-! ### The crystal operators on a row -/

lemma crystalEps_le_count (i : ℕ) (w : List ℕ) : crystalEps i w ≤ w.count i := by
  induction w with
  | nil => simp
  | cons x w ih =>
    rcases eq_or_ne x i with rfl | hne
    · rw [crystalEps_cons_self, List.count_cons_self]; omega
    · rcases eq_or_ne x (i + 1) with rfl | hne'
      · rw [crystalEps_cons_succ, List.count_cons_of_ne hne]; omega
      · rw [crystalEps_cons_of_ne hne hne', List.count_cons_of_ne hne]; exact ih

/-- In a row, no letter `i` is matched by a letter `i + 1`. -/
lemma IsRow.crystalEps_eq_count {i : ℕ} {r : List ℕ} (h : IsRow r) :
    crystalEps i r = r.count i := by
  induction r with
  | nil => simp
  | cons x r ih =>
    have hr : IsRow r := h.of_cons
    have hx : ∀ y ∈ r, x ≤ y := fun y hy => h.le_of_mem_cons hy
    rcases eq_or_ne x i with rfl | hne
    · rw [crystalEps_cons_self, List.count_cons_self, ih hr]
    · rcases eq_or_ne x (i + 1) with rfl | hne'
      · have h0 : r.count i = 0 := List.count_eq_zero.2 fun hmem => absurd (hx i hmem) (by omega)
        rw [crystalEps_cons_succ, List.count_cons_of_ne hne, ih hr, h0]
      · rw [crystalEps_cons_of_ne hne hne', List.count_cons_of_ne hne, ih hr]

/-- In a row, no letter `i + 1` is matched by a letter `i`. -/
lemma IsRow.crystalPhi_eq_count {i : ℕ} {r : List ℕ} (h : IsRow r) :
    crystalPhi i r = r.count (i + 1) := by
  have := crystalPhi_add_count i r
  rw [h.crystalEps_eq_count] at this
  omega

/-- On a row, the raising operator changes the first letter `i + 1` into an `i`. -/
lemma IsRow.crystalE_eq {i : ℕ} {r : List ℕ} (h : IsRow r) :
    crystalE i r = if r.count (i + 1) = 0 then none else some (r.set (countLt (i + 1) r) i) := by
  induction r with
  | nil => simp
  | cons x r ih =>
    have hr : IsRow r := h.of_cons
    have hx : ∀ y ∈ r, x ≤ y := fun y hy => h.le_of_mem_cons hy
    rcases lt_trichotomy x (i + 1) with hlt | rfl | hgt
    · have h1 : ¬ (x = i + 1 ∧ crystalEps i r = 0) := by rintro ⟨h1, -⟩; omega
      rw [crystalE_cons, ite_eq_right h1, ih hr, countLt_cons, ite_eq_left hlt,
        List.count_cons_of_ne (by omega)]
      by_cases h0 : r.count (i + 1) = 0
      · rw [ite_eq_left h0, ite_eq_left h0]; rfl
      · rw [ite_eq_right h0, ite_eq_right h0]; rfl
    · have hc : r.count i = 0 := List.count_eq_zero.2 fun hmem => absurd (hx i hmem) (by omega)
      have heps : crystalEps i r = 0 := by rw [hr.crystalEps_eq_count, hc]
      have hcz : countLt (i + 1) r = 0 := countLt_eq_zero_of_forall (fun y hy => hx y hy)
      have hne : ¬ (((i + 1) :: r).count (i + 1) = 0) := by
        rw [List.count_cons_self]; omega
      rw [crystalE_cons, ite_eq_left ⟨rfl, heps⟩, ite_eq_right hne, countLt_cons,
        ite_eq_right (show ¬ (i + 1 < i + 1) by omega), hcz]
      rfl
    · have hc : r.count (i + 1) = 0 :=
        List.count_eq_zero.2 fun hmem => absurd (hx _ hmem) (by omega)
      have h1 : ¬ (x = i + 1 ∧ crystalEps i r = 0) := by rintro ⟨h1, -⟩; omega
      rw [crystalE_cons, ite_eq_right h1, ih hr, ite_eq_left hc, List.count_cons_of_ne (by omega), ite_eq_left hc]
      rfl

/-- On a row, the lowering operator changes the last letter `i` into an `i + 1`. -/
lemma IsRow.crystalF_eq {i : ℕ} {r : List ℕ} (h : IsRow r) :
    crystalF i r =
      if r.count i = 0 then none else some (r.set (countLt (i + 1) r - 1) (i + 1)) := by
  induction r with
  | nil => simp
  | cons x r ih =>
    have hr : IsRow r := h.of_cons
    have hx : ∀ y ∈ r, x ≤ y := fun y hy => h.le_of_mem_cons hy
    rcases lt_trichotomy x i with hlt | rfl | hgt
    · have h1 : ¬ (x = i ∧ crystalEps i r = 0) := by rintro ⟨h1, -⟩; omega
      have h2 : ¬ (x = i + 1 ∧ crystalEps i r ≤ 1) := by rintro ⟨h1, -⟩; omega
      rw [crystalF_cons, ite_eq_right h1, ite_eq_right h2, ih hr, List.count_cons_of_ne (by omega),
        countLt_cons, ite_eq_left (show x < i + 1 by omega)]
      by_cases h0 : r.count i = 0
      · rw [ite_eq_left h0, ite_eq_left h0]; rfl
      · have hpos : 0 < countLt (i + 1) r :=
          countLt_pos_of_mem (List.count_pos_iff.1 (Nat.pos_of_ne_zero h0)) (by omega)
        rw [ite_eq_right h0, ite_eq_right h0]
        simp only [Option.map_some, Option.some_inj]
        rw [show countLt (i + 1) r + 1 - 1 = (countLt (i + 1) r - 1) + 1 by omega,
          List.set_cons_succ]
    · rcases eq_or_ne (r.count x) 0 with hc | hc
      · have heps : crystalEps x r = 0 := by rw [hr.crystalEps_eq_count, hc]
        have hcz : countLt (x + 1) r = 0 := by
          refine countLt_eq_zero_of_forall (fun y hy => ?_)
          by_cases hxy : y = x
          · subst hxy
            exact absurd (List.count_pos_iff.2 hy) (by omega)
          · have := hx y hy; omega
        have hne : ¬ ((x :: r).count x = 0) := by rw [List.count_cons_self]; omega
        rw [crystalF_cons, ite_eq_left ⟨rfl, heps⟩, ite_eq_right hne, countLt_cons,
          ite_eq_left (show x < x + 1 by omega), hcz]
        rfl
      · have heps : crystalEps x r ≠ 0 := by rw [hr.crystalEps_eq_count]; exact hc
        have hpos : 0 < countLt (x + 1) r :=
          countLt_pos_of_mem (List.count_pos_iff.1 (Nat.pos_of_ne_zero hc)) (by omega)
        have h1 : ¬ (x = x ∧ crystalEps x r = 0) := by rintro ⟨-, h1⟩; exact heps h1
        have h2 : ¬ (x = x + 1 ∧ crystalEps x r ≤ 1) := by rintro ⟨h1, -⟩; omega
        have hne : ¬ ((x :: r).count x = 0) := by rw [List.count_cons_self]; omega
        rw [crystalF_cons, ite_eq_right h1, ite_eq_right h2, ih hr, ite_eq_right hc, ite_eq_right hne, countLt_cons,
          ite_eq_left (show x < x + 1 by omega)]
        simp only [Option.map_some, Option.some_inj]
        rw [show countLt (x + 1) r + 1 - 1 = (countLt (x + 1) r - 1) + 1 by omega,
          List.set_cons_succ]
    · have hc : r.count i = 0 := List.count_eq_zero.2 fun hmem => absurd (hx _ hmem) (by omega)
      have hcc : (x :: r).count i = 0 := by rw [List.count_cons_of_ne (by omega)]; exact hc
      have h1 : ¬ (x = i ∧ crystalEps i r = 0) := by rintro ⟨h1, -⟩; omega
      rcases eq_or_ne x (i + 1) with rfl | hne
      · have heps : crystalEps i r = 0 := by rw [hr.crystalEps_eq_count, hc]
        rw [crystalF_cons, ite_eq_right h1, ite_eq_left ⟨rfl, by omega⟩, ite_eq_left hcc]
      · have h2 : ¬ (x = i + 1 ∧ crystalEps i r ≤ 1) := by rintro ⟨h1, -⟩; exact hne h1
        rw [crystalF_cons, ite_eq_right h1, ite_eq_right h2, ih hr, ite_eq_left hc, ite_eq_left hcc]
        rfl

/-! ### Rows and domination under a single change of letter -/

lemma isRow_of_getElem {r : List ℕ}
    (h : ∀ p q, (hpq : p < q) → (hq : q < r.length) → r[p]'(hpq.trans hq) ≤ r[q]) : IsRow r :=
  List.isChain_iff_pairwise.2 (List.pairwise_iff_getElem.2 (fun p q _ hq hpq => h p q hpq hq))

/-- Changing one entry of a row into a value compatible with its neighbours gives a row. -/
lemma IsRow.set {r : List ℕ} (h : IsRow r) {c v : ℕ}
    (hlt : ∀ k, (hk : k < r.length) → k < c → r[k] ≤ v)
    (hgt : ∀ k, (hk : k < r.length) → c < k → v ≤ r[k]) : IsRow (r.set c v) := by
  refine isRow_of_getElem ?_
  intro p q hpq hq
  rw [List.length_set] at hq
  rw [List.getElem_set, List.getElem_set]
  split_ifs with h1 h2 h2
  · omega
  · exact hgt q hq (by omega)
  · exact hlt p (by omega) (by omega)
  · exact h.getElem_le (le_of_lt hpq) hq

/-- Decreasing one entry of a dominated row preserves domination. -/
lemma Dominate.set_le {u r : List ℕ} {c v : ℕ} (h : Dominate u r)
    (hv : ∀ (hc : c < r.length), v ≤ r[c]) : Dominate u (r.set c v) := by
  refine dominate_of_getElem (by simpa using h.length_le) ?_
  intro k hk
  have hkr : k < r.length := lt_of_lt_of_le hk (by simpa using h.length_le)
  have hlt := h.getElem_lt k hk
  rw [List.getElem_set]
  split_ifs with hkc
  · subst hkc
    exact lt_of_le_of_lt (hv hkr) hlt
  · exact hlt

/-- Raising a letter `i` of a dominating row to `i + 1` preserves domination. -/
lemma dominate_set_succ_of_getElem_eq {d c i : ℕ} {r0 r1 : List ℕ}
    (hdom : Dominate (r1.drop d) r0) (hc : c < r1.length) (hval : r1[c] = i) :
    Dominate ((r1.set c (i + 1)).drop d) r0 := by
  refine dominate_of_getElem (by simpa using hdom.length_le) ?_
  intro k hk
  simp only [List.length_drop, List.length_set] at hk
  have hk' : k < (r1.drop d).length := by simp; omega
  have hdomk := hdom.getElem_lt k hk'
  rw [List.getElem_drop] at hdomk
  rw [List.getElem_drop, List.getElem_set]
  split_ifs with hkc
  · subst hkc; omega
  · exact hdomk

/-! ### The key two-row counting lemmas -/

/-- If the row `r1` below `r0` has more letters `i + 1` than `r0` has letters `i`, then
lowering the first letter `i + 1` of `r1` to an `i` preserves domination. -/
lemma dominate_set_countLt {i d : ℕ} {r0 r1 : List ℕ} (h0 : IsRow r0) (h1 : IsRow r1)
    (hdom : Dominate (r1.drop d) r0) (hlt : r0.count i < r1.count (i + 1)) :
    Dominate ((r1.set (countLt (i + 1) r1) i).drop d) r0 := by
  set j := countLt (i + 1) r1 with hj
  set b := r1.count (i + 1) with hb
  have hsucc : countLt (i + 1 + 1) r1 = j + b := countLt_succ (i + 1) r1
  have hjb : j + b ≤ r1.length := by
    have := countLt_le_length (i + 1 + 1) r1
    omega
  have hlen : (r1.drop d).length ≤ r0.length := hdom.length_le
  have hrow : ∀ n, (hn : n < r1.length) → j ≤ n → n < j + b → r1[n] = i + 1 := by
    intro n hn hjn hnb
    have h2 : ¬ (r1[n] < i + 1) := fun hc => by
      have := (h1.getElem_lt_iff hn (i + 1)).1 hc; omega
    have h3 : r1[n] < i + 1 + 1 := (h1.getElem_lt_iff hn (i + 1 + 1)).2 (by omega)
    omega
  refine dominate_of_getElem (by simpa using hlen) ?_
  intro k hk
  simp only [List.length_drop, List.length_set] at hk
  have hkd : d + k < r1.length := by omega
  have hk' : k < (r1.drop d).length := by simp; omega
  have hdomk := hdom.getElem_lt k hk'
  rw [List.getElem_drop] at hdomk
  rw [List.getElem_drop, List.getElem_set]
  split_ifs with hkj
  · have hj1 : r1[d + k] = i + 1 := hrow _ hkd (by omega) (by omega)
    rw [hj1] at hdomk
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 hdomk) with hlt' | heq
    · exact hlt'
    exfalso
    set A := countLt i r0 with hA
    set a := r0.count i with ha
    have hAa : countLt (i + 1) r0 = A + a := countLt_succ i r0
    have hkA : A ≤ k := by
      by_contra hc
      have : r0[k] < i := (h0.getElem_lt_iff (by omega) i).2 (by omega)
      omega
    set m := k + b - 1 with hm
    have hmr1 : d + m < r1.length := by omega
    have hmlen : m < r0.length := by
      have : m < (r1.drop d).length := by simp; omega
      omega
    have hge : r0[k] ≤ r0[m] := h0.getElem_le (by omega) hmlen
    have hdomm := hdom.getElem_lt m (by simp; omega)
    rw [List.getElem_drop] at hdomm
    have hval : r1[d + m] = i + 1 := hrow _ hmr1 (by omega) (by omega)
    rw [hval] at hdomm
    have hmlt : m < A + a := by
      rw [← hAa]
      exact (h0.getElem_lt_iff hmlen (i + 1)).1 (by omega)
    omega
  · exact hdomk

/-- If the row `r0` above `r1` has more letters `i` than `r1` has letters `i + 1`, then
raising the last letter `i` of `r0` to an `i + 1` preserves domination. -/
lemma dominate_set_countLt_pred {i d : ℕ} {r0 r1 : List ℕ} (h0 : IsRow r0) (h1 : IsRow r1)
    (hdom : Dominate (r1.drop d) r0) (hlt : r1.count (i + 1) < r0.count i) :
    Dominate (r1.drop d) (r0.set (countLt (i + 1) r0 - 1) (i + 1)) := by
  set A := countLt i r0 with hA
  set a := r0.count i with ha
  have hAa : countLt (i + 1) r0 = A + a := countLt_succ i r0
  have hA' : A + a ≤ r0.length := by
    have := countLt_le_length (i + 1) r0; omega
  set c := countLt (i + 1) r0 - 1 with hc
  have hclen : c < r0.length := by omega
  have hcval : r0[c] = i := by
    have h2 : ¬ (r0[c] < i) := fun hcon => by
      have := (h0.getElem_lt_iff hclen i).1 hcon; omega
    have h3 : r0[c] < i + 1 := (h0.getElem_lt_iff hclen (i + 1)).2 (by omega)
    omega
  refine dominate_of_getElem (by simpa using hdom.length_le) ?_
  intro k hk
  have hdomk := hdom.getElem_lt k hk
  simp only [List.length_drop] at hk
  have hkd : d + k < r1.length := by omega
  rw [List.getElem_drop] at hdomk
  rw [List.getElem_drop, List.getElem_set]
  split_ifs with hkc
  · subst hkc
    rw [hcval] at hdomk
    rcases lt_or_eq_of_le (Nat.succ_le_of_lt hdomk) with hgt | heq
    · omega
    exfalso
    set B := countLt (i + 1) r1 with hB
    set b := r1.count (i + 1) with hb
    have hsucc : countLt (i + 1 + 1) r1 = B + b := countLt_succ (i + 1) r1
    have hBle : B ≤ d + c := by
      by_contra hcon
      have : r1[d + c] < i + 1 := (h1.getElem_lt_iff hkd (i + 1)).2 (by omega)
      omega
    have hub : d + c < B + b := by
      rw [← hsucc]
      exact (h1.getElem_lt_iff hkd (i + 1 + 1)).1 (by omega)
    have hAlen : A < r0.length := by omega
    have hAval : r0[A] = i := by
      have h2 : ¬ (r0[A] < i) := fun hcon => by
        have := (h0.getElem_lt_iff hAlen i).1 hcon; omega
      have h3 : r0[A] < i + 1 := (h0.getElem_lt_iff hAlen (i + 1)).2 (by omega)
      omega
    have hAk : A < (r1.drop d).length := by simp; omega
    have hdomA := hdom.getElem_lt A hAk
    rw [List.getElem_drop, hAval] at hdomA
    have hBA : B ≤ d + A := by
      by_contra hcon
      have : r1[d + A] < i + 1 := (h1.getElem_lt_iff (by simp at hAk; omega) (i + 1)).2 (by omega)
      omega
    omega
  · exact hdomk

/-! ### Position of the letter changed in a row -/

lemma countLt_lt_length {i : ℕ} {r : List ℕ} (hc : r.count (i + 1) ≠ 0) :
    countLt (i + 1) r < r.length := by
  have h1 := countLt_succ (i + 1) r
  have h2 := countLt_le_length (i + 1 + 1) r
  omega

lemma IsRow.getElem_countLt {i : ℕ} {r : List ℕ} (h : IsRow r) (hc : r.count (i + 1) ≠ 0) :
    r[countLt (i + 1) r]'(countLt_lt_length hc) = i + 1 := by
  have hj := countLt_lt_length hc
  have h1 := countLt_succ (i + 1) r
  have h2 : ¬ (r[countLt (i + 1) r] < i + 1) := fun hcon =>
    absurd ((h.getElem_lt_iff hj (i + 1)).1 hcon) (by omega)
  have h3 : r[countLt (i + 1) r] < i + 1 + 1 := (h.getElem_lt_iff hj (i + 1 + 1)).2 (by omega)
  omega

lemma countLt_pred_lt_length {i : ℕ} {r : List ℕ} (hc : r.count i ≠ 0) :
    countLt (i + 1) r - 1 < r.length := by
  have h1 := countLt_succ i r
  have h2 := countLt_le_length (i + 1) r
  omega

lemma IsRow.getElem_countLt_pred {i : ℕ} {r : List ℕ} (h : IsRow r) (hc : r.count i ≠ 0) :
    r[countLt (i + 1) r - 1]'(countLt_pred_lt_length hc) = i := by
  have hj := countLt_pred_lt_length hc
  have h1 := countLt_succ i r
  have h2 : ¬ (r[countLt (i + 1) r - 1] < i) := fun hcon =>
    absurd ((h.getElem_lt_iff hj i).1 hcon) (by omega)
  have h3 : r[countLt (i + 1) r - 1] < i + 1 := (h.getElem_lt_iff hj (i + 1)).2 (by omega)
  omega

/-- The raising operator turns a row into a row. -/
lemma IsRow.set_countLt {i : ℕ} {r : List ℕ} (h : IsRow r) (hc : r.count (i + 1) ≠ 0) :
    IsRow (r.set (countLt (i + 1) r) i) := by
  have hval := IsRow.getElem_countLt h hc
  refine IsRow.set h (fun k hk hkc => ?_) (fun k hk hkc => ?_)
  · have : r[k] < i + 1 := (h.getElem_lt_iff hk (i + 1)).2 hkc
    omega
  · have : r[countLt (i + 1) r]'(countLt_lt_length hc) ≤ r[k] := h.getElem_le (le_of_lt hkc) hk
    omega

/-- The lowering operator turns a row into a row. -/
lemma IsRow.set_countLt_pred {i : ℕ} {r : List ℕ} (h : IsRow r) (hc : r.count i ≠ 0) :
    IsRow (r.set (countLt (i + 1) r - 1) (i + 1)) := by
  have hval := IsRow.getElem_countLt_pred h hc
  have h1 := countLt_succ i r
  refine IsRow.set h (fun k hk hkc => ?_) (fun k hk hkc => ?_)
  · have : r[k] ≤ r[countLt (i + 1) r - 1]'(countLt_pred_lt_length hc) :=
      h.getElem_le (le_of_lt hkc) (countLt_pred_lt_length hc)
    omega
  · have h2 : ¬ (r[k] < i + 1) := fun hcon =>
      absurd ((h.getElem_lt_iff hk (i + 1)).1 hcon) (by omega)
    omega

/-! ### The crystal operators preserve skew tableaux -/

/-- The raising operator sends the reading word of a skew tableau to the reading word of a
skew tableau with the same inner shape and the same shape.  The last disjunction records
where the changed letter lies: either in a row below the top one, or in the top row. -/
theorem exists_isSkewTableau_crystalE {i : ℕ} :
    ∀ {inner : List ℕ} {t : List (List ℕ)}, IsSkewTableau inner t →
      ∀ {w : List ℕ}, crystalE i (toWord t) = some w →
        ∃ t', toWord t' = w ∧ IsSkewTableau inner t' ∧ shape t' = shape t ∧
          (t'.headD [] = t.headD [] ∨
            (crystalE i (t.headD []) = some (t'.headD []) ∧
              crystalPhi i (toWord t) = crystalPhi i (t.headD []))) := by
  intro inner t
  induction t generalizing inner with
  | nil => intro _ w hw; simp at hw
  | cons r0 t ih =>
    intro ht w hw
    obtain ⟨hne, hrow0, hdom, htail⟩ := ht
    rw [toWord_cons, crystalE_append] at hw
    by_cases hcond : crystalEps i r0 < crystalPhi i (toWord t)
    · rw [ite_eq_left hcond] at hw
      obtain ⟨w0, hw0, rfl⟩ := Option.map_eq_some_iff.1 hw
      obtain ⟨t1, ht1w, ht1skew, ht1shape, hdisj⟩ := ih htail hw0
      refine ⟨r0 :: t1, by rw [toWord_cons, ht1w], ⟨hne, hrow0, ?_, ht1skew⟩,
        by rw [shape_cons, shape_cons, ht1shape], Or.inl rfl⟩
      rcases hdisj with heq | ⟨hE, hphi⟩
      · rw [SkewDominate, heq]; exact hdom
      · cases t with
        | nil => simp at hE
        | cons r1 t2 =>
          obtain ⟨-, hrow1, -, -⟩ := htail
          simp only [List.headD_cons] at hE hphi hdom
          rw [IsRow.crystalE_eq hrow1] at hE
          by_cases hc : r1.count (i + 1) = 0
          · rw [ite_eq_left hc] at hE; simp at hE
          · rw [ite_eq_right hc] at hE
            have hset : t1.headD [] = r1.set (countLt (i + 1) r1) i := by
              simp only [Option.some_inj] at hE; rw [← hE]
            rw [SkewDominate, hset]
            refine dominate_set_countLt hrow0 hrow1 hdom ?_
            have h1 : crystalEps i r0 = r0.count i := hrow0.crystalEps_eq_count
            have h2 : crystalPhi i r1 = r1.count (i + 1) := hrow1.crystalPhi_eq_count
            omega
    · rw [ite_eq_right hcond] at hw
      obtain ⟨r0', hr0', rfl⟩ := Option.map_eq_some_iff.1 hw
      rw [IsRow.crystalE_eq hrow0] at hr0'
      by_cases hc : r0.count (i + 1) = 0
      · rw [ite_eq_left hc] at hr0'; simp at hr0'
      · rw [ite_eq_right hc] at hr0'
        have hset : r0' = r0.set (countLt (i + 1) r0) i := by
          simp only [Option.some_inj] at hr0'; rw [← hr0']
        subst hset
        refine ⟨r0.set (countLt (i + 1) r0) i :: t, by rw [toWord_cons],
          ⟨by simpa using hne, IsRow.set_countLt hrow0 hc, ?_, htail⟩, by simp, Or.inr ⟨?_, ?_⟩⟩
        · refine Dominate.set_le hdom (fun hcl => ?_)
          rw [IsRow.getElem_countLt hrow0 hc]
          omega
        · simp only [List.headD_cons]
          rw [IsRow.crystalE_eq hrow0, ite_eq_right hc]
        · simp only [List.headD_cons]
          rw [toWord_cons, crystalPhi_append]
          omega

/-- The lowering operator sends the reading word of a skew tableau to the reading word of a
skew tableau with the same inner shape and the same shape. -/
theorem exists_isSkewTableau_crystalF {i : ℕ} :
    ∀ {inner : List ℕ} {t : List (List ℕ)}, IsSkewTableau inner t →
      ∀ {w : List ℕ}, crystalF i (toWord t) = some w →
        ∃ t', toWord t' = w ∧ IsSkewTableau inner t' ∧ shape t' = shape t ∧
          (t'.headD [] = t.headD [] ∨ crystalF i (t.headD []) = some (t'.headD [])) := by
  intro inner t
  induction t generalizing inner with
  | nil => intro _ w hw; simp at hw
  | cons r0 t ih =>
    intro ht w hw
    obtain ⟨hne, hrow0, hdom, htail⟩ := ht
    rw [toWord_cons, crystalF_append] at hw
    by_cases hcond : crystalPhi i (toWord t) < crystalEps i r0
    · rw [ite_eq_left hcond] at hw
      obtain ⟨r0', hr0', rfl⟩ := Option.map_eq_some_iff.1 hw
      rw [IsRow.crystalF_eq hrow0] at hr0'
      by_cases hc : r0.count i = 0
      · rw [ite_eq_left hc] at hr0'; simp at hr0'
      · rw [ite_eq_right hc] at hr0'
        have hset : r0' = r0.set (countLt (i + 1) r0 - 1) (i + 1) := by
          simp only [Option.some_inj] at hr0'; rw [← hr0']
        subst hset
        refine ⟨r0.set (countLt (i + 1) r0 - 1) (i + 1) :: t, by rw [toWord_cons],
          ⟨by simpa using hne, IsRow.set_countLt_pred hrow0 hc, ?_, htail⟩, by simp, Or.inr ?_⟩
        · cases t with
          | nil => simp [SkewDominate]
          | cons r1 t2 =>
            obtain ⟨-, hrow1, -, -⟩ := htail
            simp only [List.headD_cons] at hdom ⊢
            refine dominate_set_countLt_pred hrow0 hrow1 hdom ?_
            have h1 : crystalEps i r0 = r0.count i := hrow0.crystalEps_eq_count
            have h2 : crystalPhi i r1 = r1.count (i + 1) := hrow1.crystalPhi_eq_count
            have h3 : crystalPhi i (toWord (r1 :: t2)) = crystalPhi i (toWord t2 ++ r1) := by
              rw [toWord_cons]
            rw [h3, crystalPhi_append] at hcond
            omega
        · simp only [List.headD_cons]
          rw [IsRow.crystalF_eq hrow0, ite_eq_right hc]
    · rw [ite_eq_right hcond] at hw
      obtain ⟨w0, hw0, rfl⟩ := Option.map_eq_some_iff.1 hw
      obtain ⟨t1, ht1w, ht1skew, ht1shape, hdisj⟩ := ih htail hw0
      refine ⟨r0 :: t1, by rw [toWord_cons, ht1w], ⟨hne, hrow0, ?_, ht1skew⟩,
        by rw [shape_cons, shape_cons, ht1shape], Or.inl rfl⟩
      rcases hdisj with heq | hF
      · rw [SkewDominate, heq]; exact hdom
      · cases t with
        | nil => simp at hF
        | cons r1 t2 =>
          obtain ⟨-, hrow1, -, -⟩ := htail
          simp only [List.headD_cons] at hF hdom
          rw [IsRow.crystalF_eq hrow1] at hF
          by_cases hc : r1.count i = 0
          · rw [ite_eq_left hc] at hF; simp at hF
          · rw [ite_eq_right hc] at hF
            have hset : t1.headD [] = r1.set (countLt (i + 1) r1 - 1) (i + 1) := by
              simp only [Option.some_inj] at hF; rw [← hF]
            rw [SkewDominate, hset]
            exact dominate_set_succ_of_getElem_eq hdom (countLt_pred_lt_length hc)
              (IsRow.getElem_countLt_pred hrow1 hc)

end List
