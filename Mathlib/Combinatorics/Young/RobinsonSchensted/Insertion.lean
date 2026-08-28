/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Data.Nat.Lattice

/-!
# Schensted's row insertion and the longest nondecreasing subsequence

A Lean 4 port of the first-row part of `theories/LRrule/Schensted.v` from
[Coq-Combi](https://github.com/math-comp/Coq-Combi).

Given a word `w` over a linearly ordered alphabet, Schensted's algorithm inserts the
letters of `w` one after the other into a weakly increasing row: a letter `l` replaces
the first entry of the row that is strictly larger than `l`, and is appended at the end
of the row if there is no such entry.  Schensted's theorem states that the length of the
resulting row is the maximal length of a weakly increasing (nondecreasing) subsequence
of `w`.

## Main definitions

* `List.insPos r l` : the position at which `l` is inserted in the row `r`
  (Coq `inspos`).
* `List.insRow r l` : the row `r` after insertion of `l` (Coq `insert`).
* `List.schensted w` : the row obtained by inserting all letters of `w`, from left to
  right, into the empty row (Coq `Sch`).

## Main results

* `List.insRow_pairwise_le` : row insertion preserves rows.
* `List.schensted_exists_sublist` : the `k`-th entry of `List.schensted w` is the last
  letter of some nondecreasing subsequence of `w` of length `k + 1` (Coq `Sch_exists`).
* `List.schensted_min_last` : the `k`-th entry of `List.schensted w` is minimal among
  the last letters of the nondecreasing subsequences of `w` of length `k + 1`
  (Coq `Sch_leq_last`).
* `List.schensted_isGreatest` : Schensted's theorem, the length of `List.schensted w`
  is the maximal length of a nondecreasing subsequence of `w` (Coq `Sch_max_size`).
-/

namespace List

open List

variable {T : Type*} [LinearOrder T]

/-! ### Auxiliary facts on nondecreasing lists -/

omit [LinearOrder T] in
/-- In a nondecreasing list, every entry is at most the last one. -/
lemma le_getLast_of_pairwise_le [Preorder T] {s : List T} (hs : s.Pairwise (· ≤ ·)) {z : T}
    (hz : s.getLast? = some z) {a : T} (ha : a ∈ s) : a ≤ z := by
  induction s with
  | nil => simp at ha
  | cons b s ih =>
    rw [List.pairwise_cons] at hs
    cases s with
    | nil =>
      rw [List.getLast?_singleton, Option.some.injEq] at hz
      rw [List.mem_singleton] at ha
      subst ha
      exact le_of_eq hz
    | cons c s =>
      rw [List.getLast?_cons_cons] at hz
      rcases List.mem_cons.1 ha with rfl | ha'
      · exact hs.1 z (List.mem_of_getLast? hz)
      · exact ih hs.2 hz ha'

omit [LinearOrder T] in
/-- Monotonicity of a nondecreasing list, in terms of `getElem?`. -/
lemma pairwise_le_getElem?_mono [Preorder T] {s : List T} (hs : s.Pairwise (· ≤ ·)) {i j : ℕ}
    (hij : i ≤ j) {a b : T} (hi : s[i]? = some a) (hj : s[j]? = some b) : a ≤ b := by
  rcases eq_or_lt_of_le hij with rfl | h
  · rw [hi] at hj; exact le_of_eq (Option.some.inj hj)
  · obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.1 hi
    obtain ⟨hj', rfl⟩ := List.getElem?_eq_some_iff.1 hj
    exact List.pairwise_iff_getElem.1 hs i j hi' hj' h

/-! ### Insertion in a row -/

/-- The position of the first entry of `r` which is strictly larger than `l`; it is
`r.length` when there is no such entry (Coq `inspos`). -/
def insPos : List T → T → ℕ
  | [], _ => 0
  | x :: r, l => if l < x then 0 else insPos r l + 1

/-- Insertion of the letter `l` in the row `r`: the first entry strictly larger than `l`
is replaced by `l`, and `l` is appended if there is no such entry (Coq `insert`). -/
def insRow : List T → T → List T
  | [], l => [l]
  | x :: r, l => if l < x then l :: r else x :: insRow r l

@[simp] lemma insPos_nil (l : T) : insPos ([] : List T) l = 0 := rfl

@[simp] lemma insRow_nil (l : T) : insRow ([] : List T) l = [l] := rfl

lemma insPos_cons (x : T) (r : List T) (l : T) :
    insPos (x :: r) l = if l < x then 0 else insPos r l + 1 := rfl

lemma insRow_cons (x : T) (r : List T) (l : T) :
    insRow (x :: r) l = if l < x then l :: r else x :: insRow r l := rfl

lemma insPos_le_length (r : List T) (l : T) : insPos r l ≤ r.length := by
  induction r with
  | nil => simp
  | cons x r ih =>
    rw [insPos_cons]
    split
    · simp
    · simpa using ih

lemma insRow_length (r : List T) (l : T) :
    (insRow r l).length = max r.length (insPos r l + 1) := by
  induction r with
  | nil => simp
  | cons x r ih =>
    rw [insRow_cons, insPos_cons]
    split
    · simp
    · simp only [List.length_cons, ih]
      omega

lemma length_le_insRow_length (r : List T) (l : T) : r.length ≤ (insRow r l).length := by
  rw [insRow_length]; exact le_max_left _ _

lemma insPos_lt_insRow_length (r : List T) (l : T) : insPos r l < (insRow r l).length := by
  rw [insRow_length]
  exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)

/-- Below the insertion position, the entries of `r` are at most `l`. -/
lemma le_of_lt_insPos {r : List T} {l : T} {k : ℕ} (hk : k < insPos r l) {x : T}
    (hx : r[k]? = some x) : x ≤ l := by
  induction r generalizing k with
  | nil => simp at hx
  | cons y r ih =>
    rw [insPos_cons] at hk
    split at hk
    · omega
    · rename_i hy
      cases k with
      | zero =>
        rw [List.getElem?_cons_zero, Option.some.injEq] at hx
        exact hx ▸ not_lt.1 hy
      | succ j =>
        rw [List.getElem?_cons_succ] at hx
        exact ih (by omega) hx

/-- At the insertion position, the entry of `r` (if any) is strictly larger than `l`. -/
lemma lt_of_getElem?_insPos {r : List T} {l x : T} (hx : r[insPos r l]? = some x) : l < x := by
  induction r with
  | nil => simp at hx
  | cons y r ih =>
    rw [insPos_cons] at hx
    split at hx
    · rename_i hy
      rw [List.getElem?_cons_zero, Option.some.injEq] at hx
      exact hx ▸ hy
    · rw [List.getElem?_cons_succ] at hx
      exact ih hx

@[simp] lemma insRow_getElem?_insPos (r : List T) (l : T) :
    (insRow r l)[insPos r l]? = some l := by
  induction r with
  | nil => simp
  | cons x r ih =>
    rw [insRow_cons, insPos_cons]
    split
    · simp
    · simpa using ih

lemma insRow_getElem?_of_ne {r : List T} {l : T} {k : ℕ} (hne : k ≠ insPos r l) :
    (insRow r l)[k]? = r[k]? := by
  induction r generalizing k with
  | nil =>
    simp only [insPos_nil] at hne
    simp only [insRow_nil]
    rw [List.getElem?_eq_none (by simpa using Nat.one_le_iff_ne_zero.2 hne),
      List.getElem?_eq_none (by simp)]
  | cons x r ih =>
    rw [insPos_cons] at hne
    rw [insRow_cons]
    split at hne
    · rename_i hx
      rw [if_pos hx]
      cases k with
      | zero => exact absurd rfl hne
      | succ j => simp
    · rename_i hx
      rw [if_neg hx]
      cases k with
      | zero => simp
      | succ j =>
        simp only [List.getElem?_cons_succ]
        exact ih (by omega)

lemma mem_insRow {r : List T} {l y : T} (hy : y ∈ insRow r l) : y ∈ r ∨ y = l := by
  induction r with
  | nil =>
    simp only [insRow_nil, List.mem_singleton] at hy
    exact Or.inr hy
  | cons x r ih =>
    rw [insRow_cons] at hy
    split at hy
    · rcases List.mem_cons.1 hy with h | h
      · exact Or.inr h
      · exact Or.inl (List.mem_cons_of_mem _ h)
    · rcases List.mem_cons.1 hy with h | h
      · exact Or.inl (by simp [h])
      · rcases ih h with h' | h'
        · exact Or.inl (List.mem_cons_of_mem _ h')
        · exact Or.inr h'

/-- Row insertion preserves weakly increasing lists (Coq `is_row_insert`). -/
lemma insRow_pairwise_le {r : List T} (hr : r.Pairwise (· ≤ ·)) (l : T) :
    (insRow r l).Pairwise (· ≤ ·) := by
  induction r with
  | nil => simp
  | cons x r ih =>
    rw [List.pairwise_cons] at hr
    rw [insRow_cons]
    split
    · rename_i hx
      exact List.pairwise_cons.2 ⟨fun b hb => le_of_lt (lt_of_lt_of_le hx (hr.1 b hb)), hr.2⟩
    · rename_i hx
      refine List.pairwise_cons.2 ⟨fun b hb => ?_, ih hr.2⟩
      rcases mem_insRow hb with h | h
      · exact hr.1 b h
      · exact h ▸ not_lt.1 hx

/-! ### The Schensted row of a word -/

/-- The row obtained by inserting all the letters of `w`, from left to right, into the
empty row (Coq `Sch`). -/
def schensted (w : List T) : List T := w.foldl insRow []

@[simp] lemma schensted_nil : schensted ([] : List T) = [] := rfl

lemma schensted_concat (w : List T) (l : T) :
    schensted (w ++ [l]) = insRow (schensted w) l := by
  simp [schensted]

lemma schensted_pairwise_le (w : List T) : (schensted w).Pairwise (· ≤ ·) := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton w l ih => rw [schensted_concat]; exact insRow_pairwise_le ih l

/-- The entries of a Schensted row are weakly increasing. -/
lemma schensted_getElem_le (w : List T) {i j : ℕ} (hij : i ≤ j) (hj : j < (schensted w).length) :
    (schensted w)[i]'(lt_of_le_of_lt hij hj) ≤ (schensted w)[j] := by
  rcases eq_or_lt_of_le hij with rfl | h
  · exact le_rfl
  · exact List.pairwise_iff_getElem.1 (schensted_pairwise_le w) i j _ hj h

/-! ### Sublists ending with the last letter -/

omit [LinearOrder T] in
/-- A sublist of `w ++ [l]` either is a sublist of `w`, or is obtained from a sublist of
`w` by appending `l`. -/
lemma sublist_concat_cases {s w : List T} {l : T} (h : s.Sublist (w ++ [l])) :
    s.Sublist w ∨ ∃ s', s = s' ++ [l] ∧ s'.Sublist w := by
  obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := List.sublist_append_iff.1 h
  rcases List.sublist_singleton.1 h₂ with rfl | rfl
  · exact Or.inl (by simpa using h₁)
  · exact Or.inr ⟨l₁, rfl, h₁⟩

/-! ### Schensted's theorem -/

/-- Coq `Sch_exists`: the `k`-th entry of the Schensted row of `w` is the last letter of
a nondecreasing subsequence of `w` of length `k + 1`. -/
lemma schensted_exists_sublist (w : List T) {k : ℕ} {x : T} (hx : (schensted w)[k]? = some x) :
    ∃ s : List T, s.Sublist w ∧ s.Pairwise (· ≤ ·) ∧ s.length = k + 1 ∧
      s.getLast? = some x := by
  induction w using List.reverseRecOn generalizing k x with
  | nil => simp at hx
  | append_singleton w l ih =>
    rw [schensted_concat] at hx
    set r := schensted w with hr
    by_cases hk : k = insPos r l
    · subst hk
      rw [insRow_getElem?_insPos] at hx
      obtain rfl : l = x := Option.some.inj hx
      rcases Nat.eq_zero_or_pos (insPos r l) with hp | hp
      · refine ⟨[l], List.sublist_append_right w [l], by simp, by rw [hp]; rfl, by simp⟩
      · obtain ⟨j, hj⟩ : ∃ j, insPos r l = j + 1 := ⟨insPos r l - 1, by omega⟩
        have hjp : j < insPos r l := by omega
        have hjlen : j < r.length := lt_of_lt_of_le hjp (insPos_le_length r l)
        obtain ⟨z, hz⟩ : ∃ z, r[j]? = some z := ⟨r[j], List.getElem?_eq_getElem hjlen⟩
        have hzl : z ≤ l := le_of_lt_insPos hjp hz
        obtain ⟨s, hsub, hsort, hlen, hlast⟩ := ih hz
        refine ⟨s ++ [l], hsub.append (List.Sublist.refl _), ?_, by rw [hj]; simp [hlen],
          by simp⟩
        rw [List.pairwise_append]
        refine ⟨hsort, by simp, ?_⟩
        intro a ha b hb
        rw [List.mem_singleton] at hb
        subst hb
        exact le_trans (le_getLast_of_pairwise_le hsort hlast ha) hzl
    · rw [insRow_getElem?_of_ne hk] at hx
      obtain ⟨s, hsub, hsort, hlen, hlast⟩ := ih hx
      exact ⟨s, hsub.trans (List.sublist_append_left w [l]), hsort, hlen, hlast⟩

/-- Coq `Sch_leq_last`: among the nondecreasing subsequences of `w` of length `k + 1`,
the Schensted row has the smallest possible last letter at position `k`. -/
lemma schensted_min_last (w : List T) {k : ℕ} {s : List T} (hsub : s.Sublist w)
    (hs : s.Pairwise (· ≤ ·)) (hlen : s.length = k + 1) {y : T} (hy : s.getLast? = some y) :
    ∃ x, (schensted w)[k]? = some x ∧ x ≤ y := by
  induction w using List.reverseRecOn generalizing k s y with
  | nil =>
    rw [List.sublist_nil.1 hsub] at hlen
    simp at hlen
  | append_singleton w l ih =>
    rw [schensted_concat]
    set r := schensted w with hr
    rcases sublist_concat_cases hsub with hsw | ⟨s', rfl, hs'⟩
    · obtain ⟨x, hx, hxy⟩ := ih hsw hs hlen hy
      have hklen : k < r.length := (List.getElem?_eq_some_iff.1 hx).1
      by_cases hk : k = insPos r l
      · subst hk
        exact ⟨l, insRow_getElem?_insPos r l, le_trans (le_of_lt (lt_of_getElem?_insPos hx)) hxy⟩
      · exact ⟨x, by rw [insRow_getElem?_of_ne hk]; exact hx, hxy⟩
    · have hyl : y = l := by simpa using hy.symm
      subst hyl
      have hslen : s'.length = k := by simpa using hlen
      have hs'sort : s'.Pairwise (· ≤ ·) := (List.pairwise_append.1 hs).1
      cases k with
      | zero =>
        rcases Nat.eq_zero_or_pos (insPos r y) with hp | hp
        · refine ⟨y, ?_, le_rfl⟩
          rw [← hp]
          exact insRow_getElem?_insPos r y
        · have h0 : 0 < r.length := lt_of_lt_of_le hp (insPos_le_length r y)
          obtain ⟨z, hz⟩ : ∃ z, r[0]? = some z := ⟨r[0], List.getElem?_eq_getElem h0⟩
          refine ⟨z, ?_, le_of_lt_insPos hp hz⟩
          rw [insRow_getElem?_of_ne (by omega)]
          exact hz
      | succ j =>
        have hs'ne : s' ≠ [] := by
          intro h; rw [h] at hslen; simp at hslen
        obtain ⟨z, hz⟩ : ∃ z, s'.getLast? = some z := by
          cases h : s'.getLast? with
          | none => exact absurd (List.getLast?_eq_none_iff.1 h) hs'ne
          | some z => exact ⟨z, rfl⟩
        have hzl : z ≤ y :=
          (List.pairwise_append.1 hs).2.2 z (List.mem_of_getLast? hz) y (by simp)
        obtain ⟨x', hx', hx'z⟩ := ih hs' hs'sort hslen hz
        have hx'l : x' ≤ y := le_trans hx'z hzl
        -- the insertion position is at least `j + 1`
        have hp : j + 1 ≤ insPos r y := by
          by_contra hcon
          push_neg at hcon
          have hple : insPos r y ≤ j := by omega
          have hjlen : j < r.length := (List.getElem?_eq_some_iff.1 hx').1
          have hplen : insPos r y < r.length := lt_of_le_of_lt hple hjlen
          obtain ⟨u, hu⟩ : ∃ u, r[insPos r y]? = some u :=
            ⟨r[insPos r y], List.getElem?_eq_getElem hplen⟩
          have h1 : y < u := lt_of_getElem?_insPos hu
          have h2 : u ≤ x' := pairwise_le_getElem?_mono (schensted_pairwise_le w) hple hu hx'
          exact absurd (lt_of_lt_of_le h1 (le_trans h2 hx'l)) (lt_irrefl y)
        rcases eq_or_lt_of_le hp with heq | hlt
        · exact ⟨y, by rw [heq]; exact insRow_getElem?_insPos r y, le_rfl⟩
        · have hjlen : j + 1 < r.length := lt_of_lt_of_le hlt (insPos_le_length r y)
          obtain ⟨u, hu⟩ : ∃ u, r[j + 1]? = some u := ⟨r[j + 1], List.getElem?_eq_getElem hjlen⟩
          exact ⟨u, by rw [insRow_getElem?_of_ne (by omega)]; exact hu,
            le_of_lt_insPos hlt hu⟩

/-- Any nondecreasing subsequence of `w` is at most as long as the Schensted row of `w`. -/
lemma sublist_length_le_schensted {s w : List T} (hsub : s.Sublist w)
    (hs : s.Pairwise (· ≤ ·)) : s.length ≤ (schensted w).length := by
  cases hsne : s with
  | nil => simp
  | cons a t =>
    subst hsne
    obtain ⟨y, hy⟩ : ∃ y, (a :: t).getLast? = some y := by
      cases h : (a :: t).getLast? with
      | none => simp at h
      | some y => exact ⟨y, rfl⟩
    obtain ⟨x, hx, -⟩ := schensted_min_last w hsub hs (k := t.length) (by simp) hy
    have := (List.getElem?_eq_some_iff.1 hx).1
    simpa using this

/-- **Schensted's theorem** (Coq `Sch_max_size`): the length of the Schensted row of `w`
is the maximal length of a nondecreasing subsequence of `w`. -/
theorem schensted_isGreatest (w : List T) :
    IsGreatest {n : ℕ | ∃ s : List T, s.Sublist w ∧ s.Pairwise (· ≤ ·) ∧ s.length = n}
      (schensted w).length := by
  constructor
  · cases hlen : (schensted w).length with
    | zero => exact ⟨[], List.nil_sublist w, by simp, by simp⟩
    | succ k =>
      obtain ⟨x, hx⟩ : ∃ x, (schensted w)[k]? = some x :=
        ⟨(schensted w)[k]'(by omega), List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨s, hsub, hsort, hslen, -⟩ := schensted_exists_sublist w hx
      exact ⟨s, hsub, hsort, hslen⟩
  · rintro n ⟨s, hsub, hsort, rfl⟩
    exact sublist_length_le_schensted hsub hsort

end List
