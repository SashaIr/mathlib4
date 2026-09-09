/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.Shape.Basic

/-!
# Young tableaux

A Lean 4 port of the basic part of `theories/Combi/tableau.v` from
[Coq-Combi](https://github.com/math-comp/Coq-Combi).

Rows are lists of entries in a linearly ordered type, and a tableau is a list of
rows, listed from the longest (bottom of the recursion in the Coq sources) to the
shortest; a row *dominates* the row above it when it is entrywise strictly
larger and not longer.

## Main definitions

* `List.Dominate u v` : `u` is entrywise strictly larger than `v`, and shorter.
* `List.IsRow r` : `r` is weakly increasing.
* `List.IsTableau t` : `t` is a Young tableau.
* `List.shape t` : the shape of a tableau, as a list of row lengths.
* `List.toWord t` : the reading word of a tableau.
* `List.sizeTab t` : the number of boxes of a tableau.

## Main results

* `List.isPart_shape` : the shape of a tableau is a partition.
* `List.IsTableau.row_le` / `List.IsTableau.col_lt` : rows are weakly increasing
  and columns are strictly increasing.
* `List.IsTableau.index_le_getElem` : in a tableau of natural numbers, the entries of the
  `i`-th row are at least `i`.
* `List.length_toWord` : the reading word has one letter per box.
-/

namespace List

open List

variable {T : Type*} [LinearOrder T]

/-! ### Domination of rows -/

/-- `Dominate u v` holds when `u` is not longer than `v` and `u i > v i` for all
`i` in the range of `u` (Coq `dominate`). -/
def Dominate : List T → List T → Prop
  | [], _ => True
  | _ :: _, [] => False
  | u0 :: u, v0 :: v => v0 < u0 ∧ Dominate u v

instance decidableDominate : ∀ u v : List T, Decidable (Dominate u v)
  | [], _ => isTrue trivial
  | _ :: _, [] => isFalse id
  | _ :: u, v0 :: v =>
      letI := decidableDominate u v
      inferInstanceAs (Decidable (v0 < _ ∧ Dominate u v))

@[simp] lemma dominate_nil (v : List T) : Dominate ([] : List T) v := trivial

@[simp] lemma dominate_cons_nil (a : T) (u : List T) : ¬ Dominate (a :: u) [] := id

@[simp] lemma dominate_cons_cons {a b : T} {u v : List T} :
    Dominate (a :: u) (b :: v) ↔ b < a ∧ Dominate u v := Iff.rfl

lemma Dominate.length_le {u v : List T} (h : Dominate u v) : u.length ≤ v.length := by
  induction u generalizing v with
  | nil => simp
  | cons a u ih =>
    cases v with
    | nil => exact absurd h (dominate_cons_nil a u)
    | cons b v => simpa using ih h.2

lemma Dominate.getElem_lt {u v : List T} (h : Dominate u v) (i : ℕ) (hi : i < u.length) :
    v[i]'(lt_of_lt_of_le hi h.length_le) < u[i] := by
  induction u generalizing v i with
  | nil => simp at hi
  | cons a u ih =>
    cases v with
    | nil => exact absurd h (dominate_cons_nil a u)
    | cons b v =>
      cases i with
      | zero => simpa using h.1
      | succ j => simpa using ih h.2 j (by simpa using hi)

lemma dominate_of_getElem {u v : List T} (hlen : u.length ≤ v.length)
    (h : ∀ i, (hi : i < u.length) → v[i]'(lt_of_lt_of_le hi hlen) < u[i]) : Dominate u v := by
  induction u generalizing v with
  | nil => simp
  | cons a u ih =>
    cases v with
    | nil => simp at hlen
    | cons b v =>
      refine ⟨by simpa using h 0, ih (by simpa using hlen) ?_⟩
      intro i hi
      exact gt_iff_lt.mp (h (i+1) (Nat.add_lt_of_lt_sub hi))

lemma Dominate.trans {u v w : List T} (h1 : Dominate u v) (h2 : Dominate v w) : Dominate u w := by
  induction u generalizing v w with
  | nil => simp
  | cons a u ih =>
    cases v with
    | nil => exact absurd h1 (dominate_cons_nil a u)
    | cons b v =>
      cases w with
      | nil => exact absurd h2 (dominate_cons_nil b v)
      | cons c w => exact ⟨lt_trans h2.1 h1.1, ih h1.2 h2.2⟩

lemma Dominate.of_cons {a b : T} {u v : List T} (h : Dominate (a :: u) (b :: v)) :
    Dominate u v := h.2

/-- Coq `dominate_rcons`. -/
lemma Dominate.append_right {u v : List T} (w : List T) (h : Dominate u v) :
    Dominate u (v ++ w) := by
  induction u generalizing v with
  | nil => simp
  | cons a u ih =>
    cases v with
    | nil => exact absurd h (dominate_cons_nil a u)
    | cons b v => exact ⟨h.1, ih h.2⟩

/-- Coq `dominate_head`. -/
lemma Dominate.head_lt {u v : List T} (hu : u ≠ []) (h : Dominate u v) (d : T) :
    v.headD d < u.headD d := by
  cases u with
  | nil => exact absurd rfl hu
  | cons a u =>
    cases v with
    | nil => exact absurd h (dominate_cons_nil a u)
    | cons b v => simpa using h.1

/-! ### Rows and tableaux -/

/-- A row is a weakly increasing list. -/
def IsRow (r : List T) : Prop := List.IsChain (· ≤ ·) r

instance decidableIsRow (r : List T) : Decidable (IsRow r) :=
  inferInstanceAs (Decidable (List.IsChain (· ≤ ·) r))

@[simp] lemma isRow_nil : IsRow ([] : List T) := List.IsChain.nil

lemma IsRow.of_cons {a : T} {r : List T} (h : IsRow (a :: r)) : IsRow r :=
  List.IsChain.sublist h (List.sublist_cons_self a r)

/-- In a row, entries increase weakly along the row. -/
lemma IsRow.getElem_le {r : List T} (h : IsRow r) {i j : ℕ} (hij : i ≤ j) (hj : j < r.length) :
    r[i]'(lt_of_le_of_lt hij hj) ≤ r[j] := by
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_refl _
  · exact List.pairwise_iff_getElem.1 (List.isChain_iff_pairwise.1 h) i j _ hj hlt

/-- A Young tableau: a list of nonempty weakly increasing rows, each row being
dominated by the row above it (Coq `is_tableau`). -/
def IsTableau : List (List T) → Prop
  | [] => True
  | t0 :: t => t0 ≠ [] ∧ IsRow t0 ∧ Dominate (t.headD []) t0 ∧ IsTableau t

instance decidableIsTableau : ∀ t : List (List T), Decidable (IsTableau t)
  | [] => isTrue trivial
  | t0 :: t =>
      letI := decidableIsTableau t
      inferInstanceAs
        (Decidable (t0 ≠ [] ∧ IsRow t0 ∧ Dominate (t.headD []) t0 ∧ IsTableau t))

@[simp] lemma isTableau_nil : IsTableau ([] : List (List T)) := trivial

@[simp] lemma isTableau_cons {t0 : List T} {t : List (List T)} :
    IsTableau (t0 :: t) ↔ t0 ≠ [] ∧ IsRow t0 ∧ Dominate (t.headD []) t0 ∧ IsTableau t := Iff.rfl

lemma IsTableau.of_cons {t0 : List T} {t : List (List T)} (h : IsTableau (t0 :: t)) :
    IsTableau t := h.2.2.2

/-- The shape of a tableau: the list of the lengths of its rows. -/
def shape (t : List (List T)) : List ℕ := t.map List.length

omit [LinearOrder T] in
@[simp] lemma shape_nil : shape ([] : List (List T)) = [] := rfl

omit [LinearOrder T] in
@[simp] lemma shape_cons (r : List T) (t : List (List T)) :
    shape (r :: t) = r.length :: shape t := rfl

omit [LinearOrder T] in
/-- The shape of a list of rows has one part per row. -/
@[simp] lemma length_shape (t : List (List T)) : (shape t).length = t.length :=
  List.length_map ..

omit [LinearOrder T] in
/-- The parts of the shape are the lengths of the rows. -/
lemma getD_shape (t : List (List T)) (i : ℕ) : (shape t).getD i 0 = (t.getD i []).length := by
  rcases Nat.lt_or_ge i t.length with hi | hi
  · rw [List.getD_eq_getElem _ _ (by simpa [shape] using hi), List.getD_eq_getElem _ _ hi]
    simp [shape]
  · rw [List.getD_eq_default _ _ (by simpa [shape] using hi), List.getD_eq_default _ _ hi]
    simp

/-- The number of boxes of a tableau. -/
def sizeTab (t : List (List T)) : ℕ := (shape t).sum

/-- The reading word of a tableau: rows read from the last one to the first one. -/
def toWord (t : List (List T)) : List T := t.reverse.flatten

omit [LinearOrder T] in
@[simp] lemma toWord_nil : toWord ([] : List (List T)) = [] := rfl

omit [LinearOrder T] in
/-- Coq `to_word_cons`. -/
lemma toWord_cons (r : List T) (t : List (List T)) : toWord (r :: t) = toWord t ++ r := by
  simp [toWord]

omit [LinearOrder T] in
/-- Coq `to_word_rcons`. -/
lemma toWord_concat (t : List (List T)) (r : List T) : toWord (t ++ [r]) = r ++ toWord t := by
  simp [toWord]

/-- Coq `is_part_sht`: the shape of a tableau is a partition. -/
lemma isPart_shape {t : List (List T)} (h : IsTableau t) : IsPart (shape t) := by
  induction t with
  | nil => simp
  | cons t0 t ih =>
    obtain ⟨hne, _, hdom, htab⟩ := h
    refine ⟨?_, ih htab⟩
    cases t with
    | nil => simp [Nat.one_le_of_lt (List.length_pos_iff.2 hne)]
    | cons t1 t => simpa using hdom.length_le

omit [LinearOrder T] in
/-- Coq `size_to_word`. -/
lemma length_toWord (t : List (List T)) : (toWord t).length = sizeTab t := by
  simp [toWord, sizeTab, shape]

/-- Coq `tab0`: an empty tableau. -/
lemma IsTableau.eq_nil_of_sizeTab_eq_zero {t : List (List T)} (h : IsTableau t)
    (hs : sizeTab t = 0) : t = [] := by
  cases t with
  | nil => rfl
  | cons t0 t =>
    exfalso
    have h0 : 0 < t0.length := List.length_pos_iff.2 h.1
    simp only [sizeTab, shape_cons, List.sum_cons] at hs
    omega

/-- The rows of a tableau are rows. -/
lemma IsTableau.isRow_getD {t : List (List T)} (h : IsTableau t) (i : ℕ) :
    IsRow (t.getD i []) := by
  induction t generalizing i with
  | nil => simp
  | cons t0 t ih =>
    cases i with
    | zero => simpa using h.2.1
    | succ j => simpa using ih h.of_cons j

/-- Coq `is_tableauP`: lower rows dominate upper rows. -/
lemma IsTableau.dominate_getD {t : List (List T)} (h : IsTableau t) {i j : ℕ} (hij : i < j) :
    Dominate (t.getD j []) (t.getD i []) := by
  induction t generalizing i j with
  | nil => simp
  | cons t0 t ih =>
    obtain ⟨hne, hrow, hdom, htab⟩ := h
    have hhead : t.getD 0 [] = t.headD [] := by
      cases t <;> rfl
    cases i with
    | zero =>
      obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [hhead]; exact hdom
      · refine Dominate.trans (ih htab hk) ?_
        rw [hhead]; exact hdom
    | succ m =>
      obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      simp only [List.getD_cons_succ]
      exact ih htab (by omega)

/-- Entries increase weakly along the rows of a tableau. -/
lemma IsTableau.row_le {t : List (List T)} (h : IsTableau t) {i c c' : ℕ} (hcc : c ≤ c')
    (hc' : c' < (t.getD i []).length) :
    (t.getD i [])[c]'(lt_of_le_of_lt hcc hc') ≤ (t.getD i [])[c'] :=
  (h.isRow_getD i).getElem_le hcc hc'

/-- A pointwise criterion for being a tableau: the rows below the length are empty, each
row is weakly increasing, and each row dominates the previous one. -/
lemma isTableau_of_getD {t : List (List T)} (hne : ∀ i < t.length, t.getD i [] ≠ [])
    (hrow : ∀ i, IsRow (t.getD i [])) (hdom : ∀ i, Dominate (t.getD (i + 1) []) (t.getD i [])) :
    IsTableau t := by
  induction t with
  | nil => simp
  | cons t0 t ih =>
    have hhead : t.headD [] = t.getD 0 [] := by cases t <;> rfl
    refine ⟨hne 0 (by simp), hrow 0, ?_, ih (fun i hi => hne (i + 1) (by simpa using hi))
      (fun i => hrow (i + 1)) (fun i => hdom (i + 1))⟩
    rw [hhead]
    exact hdom 0

omit [LinearOrder T] in
/-- Two lists of lists with the same shape and the same concatenation are equal. -/
lemma eq_of_shape_eq_of_flatten_eq {P Q : List (List T)} (hsh : shape P = shape Q)
    (hf : P.flatten = Q.flatten) : P = Q := by
  induction P generalizing Q with
  | nil =>
    cases Q with
    | nil => rfl
    | cons q Q => simp [shape] at hsh
  | cons p P ih =>
    cases Q with
    | nil => simp [shape] at hsh
    | cons q Q =>
      obtain ⟨hlen, hshP⟩ : p.length = q.length ∧ shape P = shape Q := by
        simpa [shape_cons] using hsh
      simp only [List.flatten_cons] at hf
      obtain ⟨rfl, hfl⟩ := List.append_inj hf hlen
      rw [ih hshP hfl]

/-- Entries increase strictly down the columns of a tableau. -/
lemma IsTableau.col_lt {t : List (List T)} (h : IsTableau t) {i c : ℕ}
    (hc : c < (t.getD (i + 1) []).length) :
    (t.getD i [])[c]'(lt_of_lt_of_le hc (h.dominate_getD (Nat.lt_succ_self i)).length_le)
      < (t.getD (i + 1) [])[c] :=
  (h.dominate_getD (Nat.lt_succ_self i)).getElem_lt c hc

lemma IsTableau.index_le_getElem {t : List (List ℕ)} (h : IsTableau t) {i c : ℕ}
    (hc : c < (t.getD i []).length) : i ≤ (t.getD i [])[c] := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    have hlen : c < (t.getD i []).length :=
      lt_of_lt_of_le hc (h.dominate_getD (Nat.lt_succ_self i)).length_le
    exact Nat.succ_le_of_lt (lt_of_le_of_lt (ih hlen) (h.col_lt hc))

end List
