/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.Tableau.Basic
public import Mathlib.Order.Monotone.Basic

/-!
# Tableaux under a map of the alphabet

A map `f : σ → τ` of alphabets acts on tableaux entrywise.  This file defines that action
and records that a strictly monotone `f` preserves and reflects the property of being a
tableau.

## Main definitions

* `Young.mapTab f P` : the image of the tableau `P` under `f`.

## Main results

* `Young.isTableau_mapTab` : a strictly monotone map of alphabets sends tableaux to tableaux.
* `Young.isTableau_of_isTableau_mapTab` : conversely, if the image is a tableau then so is `P`.
-/

@[expose] public section

namespace Young

open List

section MapTab

variable {σ τ : Type*} [LinearOrder σ] [LinearOrder τ]

/-- The image of a tableau under a map of the alphabet. -/
def mapTab (f : σ → τ) (P : List (List σ)) : List (List τ) := P.map (List.map f)

omit [LinearOrder σ] [LinearOrder τ] in
@[simp] lemma shape_mapTab (f : σ → τ) (P : List (List σ)) : shape (mapTab f P) = shape P := by
  simp [shape, mapTab, List.map_map, Function.comp_def]

omit [LinearOrder σ] [LinearOrder τ] in
lemma getD_mapTab (f : σ → τ) (P : List (List σ)) (i : ℕ) :
    (mapTab f P).getD i [] = (P.getD i []).map f := by
  rcases Nat.lt_or_ge i P.length with h | h
  · rw [List.getD_eq_getElem _ _ (by simpa [mapTab] using h), List.getD_eq_getElem _ _ h]
    simp [mapTab]
  · rw [List.getD_eq_default _ _ (by simpa [mapTab] using h), List.getD_eq_default _ _ h]
    simp

omit [LinearOrder σ] [LinearOrder τ] in
@[simp] lemma toWord_mapTab (f : σ → τ) (P : List (List σ)) :
    toWord (mapTab f P) = (toWord P).map f := by
  simp [toWord, mapTab, List.map_reverse, List.map_flatten]

lemma isRow_map {f : σ → τ} (hf : Monotone f) {r : List σ} (hr : IsRow r) : IsRow (r.map f) := by
  rw [IsRow, List.isChain_iff_pairwise, List.pairwise_map]
  exact (List.isChain_iff_pairwise.1 hr).imp fun h => hf h

lemma dominate_map {f : σ → τ} (hf : StrictMono f) {u v : List σ} (h : Dominate u v) :
    Dominate (u.map f) (v.map f) := by
  induction u generalizing v with
  | nil => simp
  | cons a u ih =>
    cases v with
    | nil => exact absurd h (dominate_cons_nil a u)
    | cons b v => exact ⟨hf h.1, ih h.2⟩

omit [LinearOrder σ] [LinearOrder τ] in
lemma mapTab_cons (f : σ → τ) (p : List σ) (P : List (List σ)) :
    mapTab f (p :: P) = p.map f :: mapTab f P := rfl

lemma isTableau_mapTab {f : σ → τ} (hf : StrictMono f) {P : List (List σ)} (hP : IsTableau P) :
    IsTableau (mapTab f P) := by
  induction P with
  | nil => simp [mapTab]
  | cons p P ih =>
    obtain ⟨hne, hrow, hdom, htab⟩ := hP
    have hhead : (mapTab f P).headD [] = (P.headD []).map f := by
      cases P <;> rfl
    rw [mapTab_cons, isTableau_cons, hhead]
    exact ⟨by simpa using hne, isRow_map hf.monotone hrow, dominate_map hf hdom, ih htab⟩

lemma dominate_of_dominate_map {f : σ → τ} (hf : StrictMono f) {u v : List σ}
    (h : Dominate (u.map f) (v.map f)) : Dominate u v := by
  induction u generalizing v with
  | nil => simp
  | cons a u ih =>
    cases v with
    | nil => simp at h
    | cons b v => exact ⟨hf.lt_iff_lt.1 h.1, ih h.2⟩

lemma isTableau_of_isTableau_mapTab {f : σ → τ} (hf : StrictMono f) {P : List (List σ)}
    (hP : IsTableau (mapTab f P)) : IsTableau P := by
  induction P with
  | nil => simp
  | cons p P ih =>
    rw [mapTab_cons, isTableau_cons] at hP
    obtain ⟨hne, hrow, hdom, htab⟩ := hP
    have hhead : (mapTab f P).headD [] = (P.headD []).map f := by
      cases P <;> rfl
    rw [hhead] at hdom
    refine ⟨by simpa using hne, ?_, dominate_of_dominate_map hf hdom, ih htab⟩
    rw [IsRow, List.isChain_iff_pairwise]
    have := List.isChain_iff_pairwise.1 hrow
    rw [List.pairwise_map] at this
    exact this.imp fun h => hf.le_iff_le.1 h

omit [LinearOrder σ] [LinearOrder τ] in
lemma mapTab_injective {f : σ → τ} (hf : Function.Injective f) :
    Function.Injective (mapTab f) :=
  List.map_injective_iff.2 (List.map_injective_iff.2 hf)

end MapTab

end Young
