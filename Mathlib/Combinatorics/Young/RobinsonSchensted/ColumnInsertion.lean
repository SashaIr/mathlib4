/-
Copyright (c) 2026 Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import Mathlib.Combinatorics.Young.Plactic.Basic

/-!
# The number of rows of the insertion tableau

The dual of Schensted's theorem: the number of rows of the Robinson–Schensted insertion
tableau of a word `w` is the length of the longest strictly decreasing subsequence of `w`
(Coq-Combi obtains this as the first column case of the Greene invariants).

The proof follows the plactic route: the set of lengths of strictly decreasing
subsequences is invariant under the elementary Knuth transformations, a word is Knuth
equivalent to the reading word of its insertion tableau, and for the reading word of a
tableau the answer is the number of rows (the first column is strictly decreasing, and a
strictly decreasing subsequence meets each row at most once).

## Main definitions

* `List.decLengths w` : the set of lengths of the strictly decreasing subsequences of `w`.
* `List.firstCol t` : the first column of a tableau.

## Main results

* `List.decLengths_placticEquiv` : Knuth equivalent words have the same strictly
  decreasing subsequence lengths.
* `List.isGreatest_decLengths_toWord` : for a tableau, the longest strictly decreasing
  subsequence of the reading word has the length of the number of rows.
* `List.isGreatest_decLengths_RS` : the number of rows of the insertion tableau of `w` is
  the length of the longest strictly decreasing subsequence of `w`.
* `List.length_le_mul_schensted` : a word is no longer than the product of the lengths of
  its longest nondecreasing and longest strictly decreasing subsequences.
-/

namespace List

open List

variable {T : Type*} [LinearOrder T]

/-- The set of lengths of the strictly decreasing subsequences of a word. -/
def decLengths (w : List T) : Set ℕ :=
  {n | ∃ s : List T, s.Sublist w ∧ s.Pairwise (· > ·) ∧ s.length = n}

lemma zero_mem_decLengths (w : List T) : 0 ∈ decLengths w :=
  ⟨[], List.nil_sublist w, List.Pairwise.nil, rfl⟩

/-! ### Strictly decreasing subsequences of the reading word of a tableau -/

lemma length_le_one_of_pairwise {s : List T} (h1 : s.Pairwise (· ≤ ·))
    (h2 : s.Pairwise (· > ·)) : s.length ≤ 1 := by
  match s with
  | [] => simp
  | [a] => simp
  | a :: b :: t =>
    exfalso
    simp only [List.pairwise_cons, List.mem_cons] at h1 h2
    have hab1 : a ≤ b := h1.1 b (Or.inl rfl)
    have hab2 : b < a := h2.1 b (Or.inl rfl)
    order

/-- A strictly decreasing subsequence of the reading word of a tableau meets each row at
most once, hence has at most as many letters as the tableau has rows. -/
lemma length_le_of_dec_sublist_toWord {t : List (List T)} (ht : IsTableau t) {s : List T}
    (hsub : s.Sublist (toWord t)) (hdec : s.Pairwise (· > ·)) : s.length ≤ t.length := by
  induction t generalizing s with
  | nil =>
    simp only [toWord_nil] at hsub
    simp [List.sublist_nil.1 hsub]
  | cons t0 t ih =>
    rw [toWord_cons] at hsub
    obtain ⟨s1, s2, rfl, hs1, hs2⟩ := List.sublist_append_iff.1 hsub
    rw [List.pairwise_append] at hdec
    have h1 : s1.length ≤ t.length := ih ht.of_cons hs1 hdec.1
    have h2 : s2.length ≤ 1 :=
      length_le_one_of_pairwise (List.Pairwise.sublist hs2
        (List.isChain_iff_pairwise.1 ht.2.1)) hdec.2.1
    simp only [List.length_append, List.length_cons]
    omega

/-! ### The first column of a tableau -/

/-- The first column of a tableau, from the top row to the bottom one. -/
def firstCol (t : List (List T)) : List T := t.filterMap List.head?

lemma length_firstCol {t : List (List T)} (ht : IsTableau t) : (firstCol t).length = t.length := by
  induction t with
  | nil => simp [firstCol]
  | cons t0 t ih =>
    cases t0 with
    | nil => exact absurd rfl ht.1
    | cons a t0 =>
      simp only [firstCol, List.filterMap_cons, List.head?_cons, List.length_cons]
      change (firstCol t).length + 1 = t.length + 1
      rw [ih ht.of_cons]

lemma pairwise_lt_firstCol {t : List (List T)} (ht : IsTableau t) :
    (firstCol t).Pairwise (· < ·) := by
  induction t with
  | nil => simp [firstCol]
  | cons t0 t ih =>
    cases t0 with
    | nil => exact absurd rfl ht.1
    | cons a t0 =>
      simp only [firstCol, List.filterMap_cons, List.head?_cons, List.pairwise_cons]
      refine ⟨?_, ih ht.of_cons⟩
      intro b hb
      rw [List.mem_filterMap] at hb
      obtain ⟨r, hr, hrb⟩ := hb
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hr
      have hdom : Dominate (t.getD j []) ((a :: t0 : List T)) := by
        have := ht.dominate_getD (i := 0) (j := j + 1) (by omega)
        simpa [List.getD_eq_getElem _ _ hj] using this
      have hne : t.getD j [] ≠ [] := by
        intro hc
        rw [List.getD_eq_getElem _ _ hj] at hc
        rw [hc] at hrb
        simp at hrb
      have := hdom.head_lt hne a
      have hb' : (t.getD j []).headD a = b := by
        rw [List.getD_eq_getElem _ _ hj]
        cases hr' : t[j] with
        | nil => rw [hr'] at hrb; simp at hrb
        | cons c l =>
          rw [hr'] at hrb
          simp only [List.head?_cons, Option.some.injEq] at hrb
          simp [hrb]
      rw [hb'] at this
      exact this

omit [LinearOrder T] in
lemma filterMap_head?_sublist_flatten (L : List (List T)) :
    (L.filterMap List.head?).Sublist L.flatten := by
  induction L with
  | nil => simp
  | cons r L ih =>
    cases r with
    | nil => simpa using ih
    | cons a r =>
      simp only [List.filterMap_cons, List.head?_cons, List.flatten_cons, List.cons_append]
      exact List.Sublist.cons₂ a (ih.trans (List.sublist_append_right r L.flatten))

omit [LinearOrder T] in
lemma reverse_firstCol_sublist_toWord (t : List (List T)) :
    (firstCol t).reverse.Sublist (toWord t) := by
  have h := filterMap_head?_sublist_flatten t.reverse
  rwa [List.filterMap_reverse] at h

/-- For the reading word of a tableau, the longest strictly decreasing subsequence has the
length of the number of rows. -/
theorem isGreatest_decLengths_toWord {t : List (List T)} (ht : IsTableau t) :
    IsGreatest (decLengths (toWord t)) t.length := by
  constructor
  · refine ⟨(firstCol t).reverse, reverse_firstCol_sublist_toWord t, ?_, ?_⟩
    · rw [List.pairwise_reverse]
      exact pairwise_lt_firstCol ht
    · rw [List.length_reverse, length_firstCol ht]
  · rintro n ⟨s, hsub, hdec, rfl⟩
    exact length_le_of_dec_sublist_toWord ht hsub hdec

/-! ### Invariance under the Knuth transformations -/

lemma sublist_three_cases {α : Type*} {S : List α} {a b c : α} (h : S.Sublist [a, b, c]) :
    S = [] ∨ S = [a] ∨ S = [b] ∨ S = [c] ∨ S = [a, b] ∨ S = [a, c] ∨ S = [b, c] ∨
      S = [a, b, c] := by
  have h2 := List.mem_sublists.2 h
  simp [List.sublists] at h2
  tauto

lemma exists_repl_of_sublist {S B : List T} (h : S.Sublist B) (hdec : S.Pairwise (· > ·)) :
    ∃ S' : List T, S'.Sublist B ∧ S'.Pairwise (· > ·) ∧ S'.length = S.length ∧
      ∀ b ∈ S', (∃ c ∈ S, b ≤ c) ∧ (∃ c ∈ S, c ≤ b) :=
  ⟨S, h, hdec, rfl, fun b hb => ⟨⟨b, hb, le_refl b⟩, ⟨b, hb, le_refl b⟩⟩⟩

/-- Exchanging the first two letters, when the first is at most the second. -/
lemma sublist_swap12 {S : List T} {a b c : T} (hab : a ≤ b) (h : S.Sublist [a, b, c])
    (hdec : S.Pairwise (· > ·)) : S.Sublist [b, a, c] := by
  rcases sublist_three_cases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp
  · simp
  · exfalso; simp at hdec; order
  · simp
  · simp
  · exfalso; simp at hdec; order

/-- Exchanging the last two letters, when the second is at most the third. -/
lemma sublist_swap23 {S : List T} {a b c : T} (hbc : b ≤ c) (h : S.Sublist [a, b, c])
    (hdec : S.Pairwise (· > ·)) : S.Sublist [a, c, b] := by
  rcases sublist_three_cases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp
  · exfalso; simp at hdec; order
  · exfalso; simp at hdec; order

lemma repl_ac_back {x y z : T} (hxy : x ≤ y) (hyz : y < z) {S : List T}
    (h : S.Sublist [z, x, y]) (hdec : S.Pairwise (· > ·)) :
    ∃ S' : List T, S'.Sublist [x, z, y] ∧ S'.Pairwise (· > ·) ∧ S'.length = S.length ∧
      ∀ b ∈ S', (∃ c ∈ S, b ≤ c) ∧ (∃ c ∈ S, c ≤ b) := by
  rcases sublist_three_cases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact exists_repl_of_sublist (by simp) hdec
  · exact exists_repl_of_sublist (by simp) hdec
  · exact exists_repl_of_sublist (by simp) hdec
  · exact exists_repl_of_sublist (by simp) hdec
  · refine ⟨[z, y], by simp, by simpa using hyz, rfl, ?_⟩
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact ⟨⟨b, by simp, le_refl b⟩, ⟨b, by simp, le_refl b⟩⟩
    · exact ⟨⟨z, by simp, le_of_lt hyz⟩, ⟨x, by simp, hxy⟩⟩
  · exact exists_repl_of_sublist (by simp) hdec
  · exfalso; simp at hdec; order
  · exfalso; simp at hdec; order

lemma repl_ca_back {x y z : T} (hxy : x < y) (hyz : y ≤ z) {S : List T}
    (h : S.Sublist [y, z, x]) (hdec : S.Pairwise (· > ·)) :
    ∃ S' : List T, S'.Sublist [y, x, z] ∧ S'.Pairwise (· > ·) ∧ S'.length = S.length ∧
      ∀ b ∈ S', (∃ c ∈ S, b ≤ c) ∧ (∃ c ∈ S, c ≤ b) := by
  rcases sublist_three_cases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact exists_repl_of_sublist (by simp) hdec
  · exact exists_repl_of_sublist (by simp) hdec
  · exact exists_repl_of_sublist (by simp) hdec
  · exact exists_repl_of_sublist (by simp) hdec
  · exfalso; simp at hdec; order
  · exact exists_repl_of_sublist (by simp) hdec
  · refine ⟨[y, x], by simp, by simpa using hxy, rfl, ?_⟩
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact ⟨⟨z, by simp, hyz⟩, ⟨x, by simp, le_of_lt hxy⟩⟩
    · exact ⟨⟨b, by simp, le_refl b⟩, ⟨b, by simp, le_refl b⟩⟩
  · exfalso; simp at hdec; order

/-- Replacing the middle part of a word by one with the same pattern of strictly
decreasing subsequences does not change the lengths of those subsequences. -/
lemma decLengths_subset_of_middle {p s A B : List T}
    (hAB : ∀ S3 : List T, S3.Sublist A → S3.Pairwise (· > ·) →
      ∃ S3' : List T, S3'.Sublist B ∧ S3'.Pairwise (· > ·) ∧ S3'.length = S3.length ∧
        ∀ b ∈ S3', (∃ c ∈ S3, b ≤ c) ∧ (∃ c ∈ S3, c ≤ b)) :
    decLengths (p ++ (A ++ s)) ⊆ decLengths (p ++ (B ++ s)) := by
  rintro n ⟨S, hsub, hdec, rfl⟩
  obtain ⟨S1, S23, rfl, h1, h23⟩ := List.sublist_append_iff.1 hsub
  obtain ⟨S3, S4, rfl, h3, h4⟩ := List.sublist_append_iff.1 h23
  rw [List.pairwise_append] at hdec
  obtain ⟨hd1, hd34, hd134⟩ := hdec
  rw [List.pairwise_append] at hd34
  obtain ⟨hd3, hd4, hd34'⟩ := hd34
  obtain ⟨S3', hs3', hd3', hlen3', hbnd⟩ := hAB S3 h3 hd3
  refine ⟨S1 ++ (S3' ++ S4), h1.append (hs3'.append h4), ?_, by simp [hlen3']⟩
  rw [List.pairwise_append]
  refine ⟨hd1, ?_, ?_⟩
  · rw [List.pairwise_append]
    refine ⟨hd3', hd4, ?_⟩
    intro a ha b hb
    obtain ⟨-, c, hc, hca⟩ := hbnd a ha
    exact lt_of_lt_of_le (hd34' c hc b hb) hca
  · intro a ha b hb
    rcases List.mem_append.1 hb with hb | hb
    · obtain ⟨⟨c, hc, hbc⟩, -⟩ := hbnd b hb
      exact lt_of_le_of_lt hbc (hd134 a ha c (List.mem_append.2 (Or.inl hc)))
    · exact hd134 a ha b (List.mem_append.2 (Or.inr hb))

/-- The lengths of the strictly decreasing subsequences are invariant under an elementary
Knuth transformation. -/
theorem decLengths_placticStep {u v : List T} (h : PlacticStep u v) :
    decLengths u = decLengths v := by
  cases h with
  | @knuthAC x y z hxy hyz p s =>
    have hu : p ++ x :: z :: y :: s = p ++ ([x, z, y] ++ s) := by simp
    have hv : p ++ z :: x :: y :: s = p ++ ([z, x, y] ++ s) := by simp
    rw [hu, hv]
    refine Set.Subset.antisymm (decLengths_subset_of_middle ?_)
      (decLengths_subset_of_middle ?_)
    · exact fun S3 h3 hd3 => exists_repl_of_sublist
        (sublist_swap12 (le_of_lt (lt_of_le_of_lt hxy hyz)) h3 hd3) hd3
    · exact fun S3 h3 hd3 => repl_ac_back hxy hyz h3 hd3
  | @knuthCA x y z hxy hyz p s =>
    have hu : p ++ y :: x :: z :: s = p ++ ([y, x, z] ++ s) := by simp
    have hv : p ++ y :: z :: x :: s = p ++ ([y, z, x] ++ s) := by simp
    rw [hu, hv]
    refine Set.Subset.antisymm (decLengths_subset_of_middle ?_)
      (decLengths_subset_of_middle ?_)
    · exact fun S3 h3 hd3 => exists_repl_of_sublist
        (sublist_swap23 (le_of_lt (lt_of_lt_of_le hxy hyz)) h3 hd3) hd3
    · exact fun S3 h3 hd3 => repl_ca_back hxy hyz h3 hd3

/-- Knuth equivalent words have the same strictly decreasing subsequence lengths. -/
theorem decLengths_placticEquiv {u v : List T} (h : PlacticEquiv u v) :
    decLengths u = decLengths v := by
  induction h with
  | rel a b hab => exact decLengths_placticStep hab
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2

/-- The dual of Schensted's theorem: the number of rows of the insertion tableau of a word
is the length of its longest strictly decreasing subsequence. -/
theorem isGreatest_decLengths_RS (w : List T) : IsGreatest (decLengths w) (RS w).length := by
  have h := isGreatest_decLengths_toWord (isTableau_RS w)
  rwa [decLengths_placticEquiv (plactic_toWord_RS w)] at h

/-! ### The product bound -/

omit [LinearOrder T] in
lemma headD_shape (t : List (List T)) : (shape t).headD 0 = (t.headD []).length := by
  cases t <;> simp [shape]

/-- A word is no longer than the product of the length of its longest nondecreasing
subsequence by the length of its longest strictly decreasing subsequence: the insertion
tableau fits into the rectangle with these dimensions. -/
theorem length_le_mul_schensted (w : List T) :
    w.length ≤ (schensted w).length * (RS w).length := by
  have hsize : w.length = (shape (RS w)).sum := by
    rw [← sizeTab_RS w, sizeTab]
  have hpart := isPart_shape (isTableau_RS w)
  have hb : ∀ x ∈ shape (RS w), x ≤ (schensted w).length := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
    rw [← List.getD_eq_getElem _ (0 : ℕ) hi]
    calc (shape (RS w)).getD i 0 ≤ (shape (RS w)).getD 0 0 := hpart.getD_antitone (Nat.zero_le i)
      _ = (shape (RS w)).headD 0 := by cases (shape (RS w)) <;> simp
      _ = ((RS w).headD []).length := headD_shape _
      _ = (schensted w).length := by rw [headD_RS]
  have hlen : (shape (RS w)).length = (RS w).length := by simp [shape]
  calc w.length = (shape (RS w)).sum := hsize
    _ ≤ (shape (RS w)).length * (schensted w).length := by
        simpa using List.sum_le_card_nsmul (shape (RS w)) (schensted w).length hb
    _ = (schensted w).length * (RS w).length := by rw [hlen]; ring

end List
