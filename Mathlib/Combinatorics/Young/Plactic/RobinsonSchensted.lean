/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.Plactic.Basic

/-!
# Knuth equivalent words have the same insertion tableau

A Lean 4 port of the converse half of the plactic congruence theorem from
`theories/LRrule/plactic.v` of [Coq-Combi](https://github.com/math-comp/Coq-Combi).

`Mathlib/Combinatorics/Young/Plactic/Basic.lean` shows that every word is Knuth (plactic)
equivalent to the reading word of its Robinson–Schensted insertion tableau, hence that two words
with the same insertion tableau are Knuth equivalent.  Here we prove the converse: an elementary
Knuth transformation does not change the insertion tableau.  Together the two directions give
`List.placticEquiv_iff_RS_eq`, the statement that the plactic classes are exactly the fibres of the
map `List.RS`.

The proof follows Knuth's original argument.  Inserting a word `u` into a tableau `r :: t`
amounts to inserting `u` into the row `r` and inserting the word `List.bumpWord r u` of
bumped letters into `t`.  The key lemma `List.knuthRel_row` states that two words related
by one elementary Knuth transformation give the same row and bumped words which are again
related by (at most) one elementary Knuth transformation.

## Main definitions

* `List.bumpWord r u` : the word of letters bumped out of the row `r` when inserting the
  letters of `u`, one after the other.
* `List.KnuthMove` : one elementary Knuth transformation, on a three letter word.
* `List.KnuthRel` : equality or one elementary Knuth transformation, in either direction.

## Main results

* `List.knuthRel_row` : Knuth's lemma on row insertion.
* `List.RS_eq_of_placticEquiv` : Knuth equivalent words have the same insertion tableau.
* `List.placticEquiv_iff_RS_eq` : two words are Knuth equivalent if and only if they have
  the same insertion tableau.
-/

namespace List

open List

variable {T : Type*} [LinearOrder T]

/-! ### Complements on row insertion -/

lemma insRow_cons_of_lt {a l : T} (r : List T) (h : l < a) : insRow (a :: r) l = l :: r := by
  rw [insRow_cons, ite_eq_left h]

lemma insRow_cons_of_le {a l : T} (r : List T) (h : a ≤ l) :
    insRow (a :: r) l = a :: insRow r l := by
  rw [insRow_cons, ite_eq_right (not_lt.2 h)]

lemma bumped_cons_of_lt {a l : T} (r : List T) (h : l < a) : bumped (a :: r) l = some a := by
  rw [bumped_cons, ite_eq_left h]

lemma bumped_cons_of_le {a l : T} (r : List T) (h : a ≤ l) :
    bumped (a :: r) l = bumped r l := by
  rw [bumped_cons, ite_eq_right (not_lt.2 h)]

lemma mem_insRow_self (r : List T) (l : T) : l ∈ insRow r l := by
  induction r with
  | nil => simp
  | cons a r ih =>
    rw [insRow_cons]
    split
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ ih

lemma mem_of_bumped {r : List T} {l b : T} (h : bumped r l = some b) : b ∈ r :=
  List.mem_of_getElem? h

/-- The insertion position is at most any position holding an entry larger than `l`. -/
lemma insPos_le_of_lt_getElem {r : List T} {l : T} {i : ℕ} (hi : i < r.length)
    (h : l < r[i]) : insPos r l ≤ i := by
  induction r generalizing i with
  | nil => simp at hi
  | cons a r ih =>
    rw [insPos_cons]
    split
    · exact Nat.zero_le _
    · rename_i hla
      cases i with
      | zero =>
        simp only [List.getElem_cons_zero] at h
        exact absurd h hla
      | succ j =>
        simp only [List.getElem_cons_succ] at h
        have := ih (by simpa using hi) h
        omega

/-- If a row contains an entry larger than `l`, then inserting `l` bumps some entry. -/
lemma bumped_isSome_of_lt_mem {r : List T} {l c : T} (hc : c ∈ r) (hlc : l < c) :
    ∃ b, bumped r l = some b := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  have hle := insPos_le_of_lt_getElem hi hlc
  have : insPos r l < r.length := lt_of_le_of_lt hle hi
  exact ⟨r[insPos r l], List.getElem?_eq_getElem this⟩

lemma bumped_eq_none_of_forall_le' {r : List T} {l : T} (h : ∀ c ∈ r, c ≤ l) :
    bumped r l = none := by
  rcases hb : bumped r l with _ | b
  · rfl
  · exact absurd (h b (mem_of_bumped hb)) (not_le.2 (lt_of_bumped hb))

/-- The bumped entry is the smallest entry of the row which is larger than `l`. -/
lemma bumped_le_of_lt_mem {r : List T} (hr : IsRow r) {l b c : T} (hb : bumped r l = some b)
    (hc : c ∈ r) (hlc : l < c) : b ≤ c := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  have hle := insPos_le_of_lt_getElem hi hlc
  have hb' : r[insPos r l]'(lt_of_le_of_lt hle hi) = b := by
    have := bumped_eq_getElem hb
    simpa using this.symm
  rw [← hb']
  exact hr.getElem_le hle hi

lemma IsRow.head_le {a : T} {r : List T} (h : IsRow (a :: r)) {c : T} (hc : c ∈ r) : a ≤ c := by
  have := List.isChain_iff_pairwise.1 h
  rw [List.pairwise_cons] at this
  exact this.1 c hc

/-! ### The word of bumped letters -/

/-- The letters bumped out of the row `r` when the letters of `u` are inserted one after
the other, in order. -/
def bumpWord (r : List T) : List T → List T
  | [] => []
  | l :: u => (bumped r l).toList ++ bumpWord (insRow r l) u

@[simp] lemma bumpWord_nil (r : List T) : bumpWord r ([] : List T) = [] := rfl

lemma bumpWord_cons (r : List T) (l : T) (u : List T) :
    bumpWord r (l :: u) = (bumped r l).toList ++ bumpWord (insRow r l) u := rfl

lemma bumpWord_length_le (r : List T) (u : List T) : (bumpWord r u).length ≤ u.length := by
  induction u generalizing r with
  | nil => simp
  | cons l u ih =>
    rw [bumpWord_cons, List.length_append, List.length_cons]
    have : (bumped r l).toList.length ≤ 1 := by cases bumped r l <;> simp
    have := ih (insRow r l)
    omega

lemma bumpWord_nil_length_lt {u : List T} (hu : u ≠ []) :
    (bumpWord ([] : List T) u).length < u.length := by
  cases u with
  | nil => exact absurd rfl hu
  | cons l u =>
    rw [bumpWord_cons]
    have : bumped ([] : List T) l = none := rfl
    rw [this]
    simpa using Nat.lt_succ_of_le (bumpWord_length_le [l] u)

/-- Inserting a word in a tableau: the first row absorbs the word, and the bumped letters
are inserted in the remaining rows. -/
lemma foldl_insTab_cons (r : List T) (t : List (List T)) (u : List T) :
    List.foldl insTab (r :: t) u
      = List.foldl insRow r u :: List.foldl insTab t (bumpWord r u) := by
  induction u generalizing r t with
  | nil => simp
  | cons l u ih =>
    rw [List.foldl_cons, bumpWord_cons, List.foldl_append, List.foldl_cons]
    rcases hb : bumped r l with _ | b
    · rw [insTab_cons_of_bumped_none hb, ih]
      simp
    · rw [insTab_cons_of_bumped_some hb, ih]
      simp

lemma foldl_insTab_nil_cons (l : T) (u : List T) :
    List.foldl insTab ([] : List (List T)) (l :: u)
      = List.foldl insRow [] (l :: u)
        :: List.foldl insTab [] (bumpWord ([] : List T) (l :: u)) := by
  have hb : bumped ([] : List T) l = none := rfl
  rw [List.foldl_cons, bumpWord_cons, hb]
  have : insTab ([] : List (List T)) l = [l] :: [] := rfl
  rw [this, foldl_insTab_cons]
  simp [insRow]

/-! ### Elementary Knuth transformations -/

/-- One elementary Knuth transformation on a three letter word. -/
inductive KnuthMove : List T → List T → Prop
  | ac {x y z : T} (hxy : x ≤ y) (hyz : y < z) : KnuthMove [x, z, y] [z, x, y]
  | ca {x y z : T} (hxy : x < y) (hyz : y ≤ z) : KnuthMove [y, x, z] [y, z, x]

/-- Two words are related if they are equal or differ by one elementary Knuth
transformation. -/
def KnuthRel (u v : List T) : Prop := u = v ∨ KnuthMove u v ∨ KnuthMove v u

lemma KnuthRel.refl (u : List T) : KnuthRel u u := Or.inl rfl

lemma KnuthRel.symm {u v : List T} (h : KnuthRel u v) : KnuthRel v u := by
  rcases h with rfl | h | h
  · exact Or.inl rfl
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

lemma KnuthMove.length_eq_three {u v : List T} (h : KnuthMove u v) : u.length = 3 := by
  cases h <;> rfl

/-- Words of length at most two which are Knuth related are equal. -/
lemma KnuthRel.eq_of_length_le_two {u v : List T} (h : KnuthRel u v) (hu : u.length ≤ 2) :
    u = v := by
  rcases h with rfl | h | h
  · rfl
  · exact absurd h.length_eq_three (by omega)
  · have : v.length = 3 := h.length_eq_three
    have : u.length = 3 := by
      have := h; cases this <;> simp_all
    omega

lemma KnuthMove.placticStep {u v : List T} (h : KnuthMove u v) : PlacticStep u v := by
  cases h with
  | ac hxy hyz => simpa using PlacticStep.knuthAC hxy hyz [] []
  | ca hxy hyz => simpa using PlacticStep.knuthCA hxy hyz [] []

/-! ### Knuth's lemma on row insertion -/

/-- Peeling off an entry of the row which is at most all the inserted letters. -/
lemma foldl_insRow_cons_of_forall_le {a : T} (r : List T) {u : List T}
    (h : ∀ l ∈ u, a ≤ l) : List.foldl insRow (a :: r) u = a :: List.foldl insRow r u := by
  induction u generalizing r with
  | nil => simp
  | cons l u ih =>
    rw [List.foldl_cons, List.foldl_cons, insRow_cons_of_le r (h l (List.mem_cons_self ..))]
    exact ih _ fun m hm => h m (List.mem_cons_of_mem _ hm)

lemma bumpWord_cons_of_forall_le {a : T} (r : List T) {u : List T}
    (h : ∀ l ∈ u, a ≤ l) : bumpWord (a :: r) u = bumpWord r u := by
  induction u generalizing r with
  | nil => simp
  | cons l u ih =>
    have hal : a ≤ l := h l (List.mem_cons_self ..)
    rw [bumpWord_cons, bumpWord_cons, bumped_cons_of_le r hal, insRow_cons_of_le r hal,
      ih _ fun m hm => h m (List.mem_cons_of_mem _ hm)]

/-- Inserting a letter smaller than every entry of the row replaces the first entry. -/
lemma insRow_of_forall_lt {r : List T} {l : T} (h : ∀ c ∈ r, l < c) :
    insRow r l = l :: r.tail := by
  cases r with
  | nil => rfl
  | cons a r => rw [insRow_cons_of_lt r (h a (List.mem_cons_self ..))]; rfl

lemma bumped_of_forall_lt {r : List T} {l : T} (h : ∀ c ∈ r, l < c) :
    bumped r l = r.head? := by
  cases r with
  | nil => rfl
  | cons a r => rw [bumped_cons_of_lt r (h a (List.mem_cons_self ..))]; rfl

/-- Knuth's lemma for the first elementary transformation. -/
lemma knuthMove_ac_row {r : List T} (hr : IsRow r) {x y z : T} (hxy : x ≤ y) (hyz : y < z) :
    List.foldl insRow r [x, z, y] = List.foldl insRow r [z, x, y] ∧
      KnuthRel (bumpWord r [x, z, y]) (bumpWord r [z, x, y]) := by
  have hxz : x < z := lt_of_le_of_lt hxy hyz
  revert hr
  induction r with
  | nil =>
    intro _
    have e1 : insRow ([] : List T) x = [x] := rfl
    have e2 : insRow [x] z = [x, z] := by rw [insRow_cons_of_le [] hxz.le]; rfl
    have e3 : insRow [x, z] y = [x, y] := by
      rw [insRow_cons_of_le _ hxy, insRow_cons_of_lt _ hyz]
    have e2b : bumped [x] z = none := by
      rw [bumped_cons_of_le [] hxz.le]; rfl
    have e3b : bumped [x, z] y = some z := by
      rw [bumped_cons_of_le _ hxy, bumped_cons_of_lt _ hyz]
    have f1 : insRow ([] : List T) z = [z] := rfl
    have f2 : insRow [z] x = [x] := insRow_cons_of_lt [] hxz
    have f2b : bumped [z] x = some z := bumped_cons_of_lt [] hxz
    have f3 : insRow [x] y = [x, y] := by rw [insRow_cons_of_le [] hxy]; rfl
    have f3b : bumped [x] y = none := by rw [bumped_cons_of_le [] hxy]; rfl
    refine ⟨?_, ?_⟩
    · simp only [List.foldl_cons, List.foldl_nil, e1, e2, e3, f1, f2, f3]
    · simp only [bumpWord_cons, bumpWord_nil, List.append_nil, e1, e2, e2b, e3b, f1, f2, f2b, f3b,
        Option.toList_none, Option.toList_some, List.nil_append, List.append_nil]
      exact KnuthRel.refl _
  | cons a r ih =>
    intro hr
    have hrr : IsRow r := hr.of_cons
    have har : ∀ c ∈ r, a ≤ c := fun c hc => hr.head_le hc
    rcases le_or_gt a x with hax | hxa
    · have hall : ∀ l ∈ [x, z, y], a ≤ l := by
        intro l hl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl
        · exact hax
        · exact hax.trans hxz.le
        · exact hax.trans hxy
      have hall' : ∀ l ∈ [z, x, y], a ≤ l := by
        intro l hl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl
        · exact hax.trans hxz.le
        · exact hax
        · exact hax.trans hxy
      obtain ⟨h1, h2⟩ := ih hrr
      refine ⟨?_, ?_⟩
      · rw [foldl_insRow_cons_of_forall_le r hall, foldl_insRow_cons_of_forall_le r hall', h1]
      · rw [bumpWord_cons_of_forall_le r hall, bumpWord_cons_of_forall_le r hall']
        exact h2
    · rcases lt_or_ge z a with hza | haz
      · have hzr : ∀ c ∈ r, z < c := fun c hc => lt_of_lt_of_le hza (har c hc)
        have hyr : ∀ c ∈ r, y < c := fun c hc => hyz.trans (hzr c hc)
        have e1 : insRow (a :: r) x = x :: r := insRow_cons_of_lt r hxa
        have e1b : bumped (a :: r) x = some a := bumped_cons_of_lt r hxa
        have e2 : insRow (x :: r) z = x :: z :: r.tail := by
          rw [insRow_cons_of_le r hxz.le, insRow_of_forall_lt hzr]
        have e2b : bumped (x :: r) z = r.head? := by
          rw [bumped_cons_of_le r hxz.le, bumped_of_forall_lt hzr]
        have e3 : insRow (x :: z :: r.tail) y = x :: y :: r.tail := by
          rw [insRow_cons_of_le _ hxy, insRow_cons_of_lt _ hyz]
        have e3b : bumped (x :: z :: r.tail) y = some z := by
          rw [bumped_cons_of_le _ hxy, bumped_cons_of_lt _ hyz]
        have f1 : insRow (a :: r) z = z :: r := insRow_cons_of_lt r hza
        have f1b : bumped (a :: r) z = some a := bumped_cons_of_lt r hza
        have f2 : insRow (z :: r) x = x :: r := insRow_cons_of_lt r hxz
        have f2b : bumped (z :: r) x = some z := bumped_cons_of_lt r hxz
        have f3 : insRow (x :: r) y = x :: y :: r.tail := by
          rw [insRow_cons_of_le r hxy, insRow_of_forall_lt hyr]
        have f3b : bumped (x :: r) y = r.head? := by
          rw [bumped_cons_of_le r hxy, bumped_of_forall_lt hyr]
        refine ⟨?_, ?_⟩
        · simp only [List.foldl_cons, List.foldl_nil, e1, e2, e3, f1, f2, f3]
        · simp only [bumpWord_cons, bumpWord_nil, List.append_nil, e1, e1b, e2, e2b, e3, e3b,
            f1, f1b, f2, f2b, f3b, Option.toList_some, List.cons_append, List.nil_append]
          rcases hh : r.head? with _ | h
          · exact Or.inl (by simp)
          · have hmem : h ∈ r := List.mem_of_mem_head? hh
            simp only [Option.toList_some, List.cons_append, List.nil_append]
            exact Or.inr (Or.inr (KnuthMove.ca hza (har h hmem)))
      · have e1 : insRow (a :: r) x = x :: r := insRow_cons_of_lt r hxa
        have e1b : bumped (a :: r) x = some a := bumped_cons_of_lt r hxa
        have e2 : insRow (x :: r) z = x :: insRow r z := insRow_cons_of_le r hxz.le
        have e2b : bumped (x :: r) z = bumped r z := bumped_cons_of_le r hxz.le
        have e3 : insRow (x :: insRow r z) y = x :: insRow (insRow r z) y :=
          insRow_cons_of_le _ hxy
        have e3b : bumped (x :: insRow r z) y = bumped (insRow r z) y :=
          bumped_cons_of_le _ hxy
        have f1 : insRow (a :: r) z = a :: insRow r z := insRow_cons_of_le r haz
        have f1b : bumped (a :: r) z = bumped r z := bumped_cons_of_le r haz
        have f2 : insRow (a :: insRow r z) x = x :: insRow r z := insRow_cons_of_lt _ hxa
        have f2b : bumped (a :: insRow r z) x = some a := bumped_cons_of_lt _ hxa
        refine ⟨?_, ?_⟩
        · simp only [List.foldl_cons, List.foldl_nil, e1, e2, e3, f1, f2]
        · simp only [bumpWord_cons, bumpWord_nil, List.append_nil, e1, e1b, e2, e2b, e3, e3b,
            f1, f1b, f2, f2b]
          rcases hc : bumped r z with _ | c
          · exact Or.inl (by simp)
          · obtain ⟨d, hd⟩ := bumped_isSome_of_lt_mem (mem_insRow_self r z) hyz
            have hdmem : d ∈ insRow r z := mem_of_bumped hd
            have had : a ≤ d := by
              rcases mem_insRow hdmem with h | h
              · exact har d h
              · exact h ▸ haz
            have hdz : d ≤ z :=
              bumped_le_of_lt_mem (isRow_insRow hrr z) hd (mem_insRow_self r z) hyz
            have hdc : d < c := lt_of_le_of_lt hdz (lt_of_bumped hc)
            simp only [hd, Option.toList_some, List.cons_append, List.nil_append]
            exact Or.inr (Or.inl (KnuthMove.ac had hdc))

/-- Knuth's lemma for the second elementary transformation. -/
lemma knuthMove_ca_row {r : List T} (hr : IsRow r) {x y z : T} (hxy : x < y) (hyz : y ≤ z) :
    List.foldl insRow r [y, x, z] = List.foldl insRow r [y, z, x] ∧
      KnuthRel (bumpWord r [y, x, z]) (bumpWord r [y, z, x]) := by
  have hxz : x < z := lt_of_lt_of_le hxy hyz
  revert hr
  induction r with
  | nil =>
    intro _
    have e1 : insRow ([] : List T) y = [y] := rfl
    have e2 : insRow [y] x = [x] := insRow_cons_of_lt [] hxy
    have e2b : bumped [y] x = some y := bumped_cons_of_lt [] hxy
    have e3 : insRow [x] z = [x, z] := by rw [insRow_cons_of_le [] hxz.le]; rfl
    have e3b : bumped [x] z = none := by rw [bumped_cons_of_le [] hxz.le]; rfl
    have f2 : insRow [y] z = [y, z] := by rw [insRow_cons_of_le [] hyz]; rfl
    have f2b : bumped [y] z = none := by rw [bumped_cons_of_le [] hyz]; rfl
    have f3 : insRow [y, z] x = [x, z] := insRow_cons_of_lt _ hxy
    have f3b : bumped [y, z] x = some y := bumped_cons_of_lt _ hxy
    refine ⟨?_, ?_⟩
    · simp only [List.foldl_cons, List.foldl_nil, e1, e2, e3, f2, f3]
    · simp only [bumpWord_cons, bumpWord_nil, List.append_nil, e1, e2, e2b, e3b, f2, f2b, f3b,
        Option.toList_none, Option.toList_some, List.nil_append, List.append_nil]
      exact KnuthRel.refl _
  | cons a r ih =>
    intro hr
    have hrr : IsRow r := hr.of_cons
    have har : ∀ c ∈ r, a ≤ c := fun c hc => hr.head_le hc
    rcases le_or_gt a x with hax | hxa
    · have hall : ∀ l ∈ [y, x, z], a ≤ l := by
        intro l hl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl
        · exact hax.trans hxy.le
        · exact hax
        · exact hax.trans hxz.le
      have hall' : ∀ l ∈ [y, z, x], a ≤ l := by
        intro l hl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl
        · exact hax.trans hxy.le
        · exact hax.trans hxz.le
        · exact hax
      obtain ⟨h1, h2⟩ := ih hrr
      refine ⟨?_, ?_⟩
      · rw [foldl_insRow_cons_of_forall_le r hall, foldl_insRow_cons_of_forall_le r hall', h1]
      · rw [bumpWord_cons_of_forall_le r hall, bumpWord_cons_of_forall_le r hall']
        exact h2
    · rcases lt_or_ge y a with hya | hay
      · have e1 : insRow (a :: r) y = y :: r := insRow_cons_of_lt r hya
        have e1b : bumped (a :: r) y = some a := bumped_cons_of_lt r hya
        have e2 : insRow (y :: r) x = x :: r := insRow_cons_of_lt r hxy
        have e2b : bumped (y :: r) x = some y := bumped_cons_of_lt r hxy
        have e3 : insRow (x :: r) z = x :: insRow r z := insRow_cons_of_le r hxz.le
        have e3b : bumped (x :: r) z = bumped r z := bumped_cons_of_le r hxz.le
        have f2 : insRow (y :: r) z = y :: insRow r z := insRow_cons_of_le r hyz
        have f2b : bumped (y :: r) z = bumped r z := bumped_cons_of_le r hyz
        have f3 : insRow (y :: insRow r z) x = x :: insRow r z := insRow_cons_of_lt _ hxy
        have f3b : bumped (y :: insRow r z) x = some y := bumped_cons_of_lt _ hxy
        refine ⟨?_, ?_⟩
        · simp only [List.foldl_cons, List.foldl_nil, e1, e2, e3, f2, f3]
        · simp only [bumpWord_cons, bumpWord_nil, List.append_nil, e1, e1b, e2, e2b, e3, e3b,
            f2, f2b, f3, f3b, Option.toList_some, List.cons_append, List.nil_append]
          rcases hc : bumped r z with _ | c
          · exact Or.inl (by simp)
          · have hmem : c ∈ r := mem_of_bumped hc
            simp only [Option.toList_some, List.cons_append, List.nil_append]
            exact Or.inr (Or.inl (KnuthMove.ca hya (har c hmem)))
      · have e1 : insRow (a :: r) y = a :: insRow r y := insRow_cons_of_le r hay
        have e1b : bumped (a :: r) y = bumped r y := bumped_cons_of_le r hay
        have e2 : insRow (a :: insRow r y) x = x :: insRow r y := insRow_cons_of_lt _ hxa
        have e2b : bumped (a :: insRow r y) x = some a := bumped_cons_of_lt _ hxa
        have e3 : insRow (x :: insRow r y) z = x :: insRow (insRow r y) z :=
          insRow_cons_of_le _ hxz.le
        have e3b : bumped (x :: insRow r y) z = bumped (insRow r y) z :=
          bumped_cons_of_le _ hxz.le
        have f2 : insRow (a :: insRow r y) z = a :: insRow (insRow r y) z :=
          insRow_cons_of_le _ (hay.trans hyz)
        have f2b : bumped (a :: insRow r y) z = bumped (insRow r y) z :=
          bumped_cons_of_le _ (hay.trans hyz)
        have f3 : insRow (a :: insRow (insRow r y) z) x = x :: insRow (insRow r y) z :=
          insRow_cons_of_lt _ hxa
        have f3b : bumped (a :: insRow (insRow r y) z) x = some a := bumped_cons_of_lt _ hxa
        refine ⟨?_, ?_⟩
        · simp only [List.foldl_cons, List.foldl_nil, e1, e2, e3, f2, f3]
        · simp only [bumpWord_cons, bumpWord_nil, List.append_nil, e1, e1b, e2, e2b, e3, e3b,
            f2, f2b, f3, f3b]
          rcases hd : bumped (insRow r y) z with _ | d
          · exact Or.inl (by simp)
          · have hdmem : d ∈ insRow r y := mem_of_bumped hd
            have hzd : z < d := lt_of_bumped hd
            have hyd : y < d := lt_of_le_of_lt hyz hzd
            have hdr : d ∈ r := by
              rcases mem_insRow hdmem with h | h
              · exact h
              · exact absurd h (ne_of_gt hyd)
            obtain ⟨c, hc⟩ := bumped_isSome_of_lt_mem hdr hyd
            have hac : a < c := lt_of_le_of_lt hay (lt_of_bumped hc)
            have hcd : c ≤ d := bumped_le_of_lt_mem hrr hc hdr hyd
            simp only [hc, Option.toList_some, List.cons_append, List.nil_append]
            exact Or.inr (Or.inl (KnuthMove.ca hac hcd))

/-- Knuth's lemma: inserting two Knuth related words in a row gives the same row, and the
bumped words are again Knuth related. -/
lemma knuthRel_row {r : List T} (hr : IsRow r) {u v : List T} (h : KnuthRel u v) :
    List.foldl insRow r u = List.foldl insRow r v ∧ KnuthRel (bumpWord r u) (bumpWord r v) := by
  rcases h with rfl | h | h
  · exact ⟨rfl, KnuthRel.refl _⟩
  · cases h with
    | ac hxy hyz => exact knuthMove_ac_row hr hxy hyz
    | ca hxy hyz => exact knuthMove_ca_row hr hxy hyz
  · cases h with
    | ac hxy hyz =>
      obtain ⟨h1, h2⟩ := knuthMove_ac_row hr hxy hyz
      exact ⟨h1.symm, h2.symm⟩
    | ca hxy hyz =>
      obtain ⟨h1, h2⟩ := knuthMove_ca_row hr hxy hyz
      exact ⟨h1.symm, h2.symm⟩

/-! ### Knuth related words have the same insertion tableau -/

lemma foldl_insTab_eq_of_knuthRel :
    ∀ (t : List (List T)), IsTableau t → ∀ {u v : List T}, KnuthRel u v →
      List.foldl insTab t u = List.foldl insTab t v := by
  intro t
  induction t with
  | nil =>
    intro _ u v h
    rcases eq_or_ne u v with rfl | hne
    · rfl
    · have hu : u ≠ [] := by
        rintro rfl
        exact hne (h.eq_of_length_le_two (by simp))
      have hv : v ≠ [] := by
        rintro rfl
        exact hne (h.symm.eq_of_length_le_two (by simp)).symm
      obtain ⟨l, u, rfl⟩ := List.exists_cons_of_ne_nil hu
      obtain ⟨m, v, rfl⟩ := List.exists_cons_of_ne_nil hv
      obtain ⟨hrow, hb⟩ := knuthRel_row (isRow_nil (T := T)) h
      have hlen : (bumpWord ([] : List T) (l :: u)).length ≤ 2 := by
        have h3 : (l :: u).length = 3 := by
          rcases h with heq | hm | hm
          · exact absurd heq hne
          · exact hm.length_eq_three
          · have := hm.length_eq_three
            have := hm.placticStep.perm.length_eq
            omega
        have := bumpWord_nil_length_lt (u := l :: u) (by simp)
        omega
      rw [foldl_insTab_nil_cons, foldl_insTab_nil_cons, hrow, hb.eq_of_length_le_two hlen]
  | cons r t ih =>
    intro ht u v h
    obtain ⟨-, hrow, -, ht'⟩ := ht
    obtain ⟨h1, h2⟩ := knuthRel_row hrow h
    rw [foldl_insTab_cons, foldl_insTab_cons, h1, ih ht' h2]

/-- An elementary Knuth transformation does not change the insertion tableau. -/
theorem RS_eq_of_placticStep {u v : List T} (h : PlacticStep u v) : RS u = RS v := by
  cases h with
  | @knuthAC x y z hxy hyz p s =>
    change List.foldl insTab [] _ = List.foldl insTab [] _
    have hp : IsTableau (List.foldl insTab ([] : List (List T)) p) := isTableau_RS p
    have : List.foldl insTab (List.foldl insTab ([] : List (List T)) p) [x, z, y]
        = List.foldl insTab (List.foldl insTab ([] : List (List T)) p) [z, x, y] :=
      foldl_insTab_eq_of_knuthRel _ hp (Or.inr (Or.inl (KnuthMove.ac hxy hyz)))
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at this ⊢
    rw [this]
  | @knuthCA x y z hxy hyz p s =>
    change List.foldl insTab [] _ = List.foldl insTab [] _
    have hp : IsTableau (List.foldl insTab ([] : List (List T)) p) := isTableau_RS p
    have : List.foldl insTab (List.foldl insTab ([] : List (List T)) p) [y, x, z]
        = List.foldl insTab (List.foldl insTab ([] : List (List T)) p) [y, z, x] :=
      foldl_insTab_eq_of_knuthRel _ hp (Or.inr (Or.inl (KnuthMove.ca hxy hyz)))
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at this ⊢
    rw [this]

/-- Knuth equivalent words have the same insertion tableau (Coq `plactic_RS`). -/
theorem RS_eq_of_placticEquiv {u v : List T} (h : PlacticEquiv u v) : RS u = RS v := by
  induction h with
  | rel _ _ h => exact RS_eq_of_placticStep h
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-- Two words are Knuth equivalent if and only if they have the same insertion tableau:
the plactic classes are the fibres of the Robinson–Schensted map (Coq `plactic_RS`). -/
theorem placticEquiv_iff_RS_eq {u v : List T} : PlacticEquiv u v ↔ RS u = RS v :=
  ⟨RS_eq_of_placticEquiv, plactic_of_RS_eq⟩

end List
