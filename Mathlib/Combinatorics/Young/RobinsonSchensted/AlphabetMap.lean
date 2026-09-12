/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.RobinsonSchensted.InsertionTableau
public import Mathlib.Combinatorics.Young.Tableau.Map

/-!
# Schensted insertion under a map of the alphabet

A strictly monotone map `f : σ → τ` of alphabets commutes with Schensted insertion: it
sends the insertion position, the bumped letter, the row insertion `insRow`, the tableau
insertion `insTab` and hence the insertion tableau `RS` of a word to their analogues over
the alphabet `τ`.

## Main results

* `Young.insRow_map` : `insRow (r.map f) (f l) = (insRow r l).map f`.
* `Young.insTab_mapTab` : `insTab (mapTab f P) (f l) = mapTab f (insTab P l)`.
* `Young.RS_map` : `RS (w.map f) = mapTab f (RS w)`.
-/

@[expose] public section

namespace Young

open List

section MapRS

variable {σ τ : Type*} [LinearOrder σ] [LinearOrder τ] {f : σ → τ} (hf : StrictMono f)
include hf

/-- A strictly monotone map of the alphabet preserves the insertion position. -/
lemma insPos_map (r : List σ) (l : σ) : insPos (r.map f) (f l) = insPos r l := by
  induction r with
  | nil => simp
  | cons x r ih => simp only [List.map_cons, insPos_cons, hf.lt_iff_lt, ih]

/-- A strictly monotone map of the alphabet commutes with row insertion. -/
lemma insRow_map (r : List σ) (l : σ) : insRow (r.map f) (f l) = (insRow r l).map f := by
  induction r with
  | nil => simp
  | cons x r ih =>
      simp only [List.map_cons, insRow_cons, hf.lt_iff_lt]
      split
      · simp
      · simp [ih]

/-- A strictly monotone map of the alphabet commutes with the bumped letter. -/
lemma bumped_map (r : List σ) (l : σ) : bumped (r.map f) (f l) = (bumped r l).map f := by
  rw [bumped, bumped, insPos_map hf, List.getElem?_map]

/-- A strictly monotone map of the alphabet commutes with insertion in a tableau. -/
lemma insTab_mapTab (P : List (List σ)) (l : σ) :
    insTab (mapTab f P) (f l) = mapTab f (insTab P l) := by
  induction P generalizing l with
  | nil => simp [mapTab]
  | cons p P ih =>
      rw [mapTab_cons, insTab, insTab, bumped_map hf]
      cases hb : bumped p l with
      | none => simp [mapTab_cons, insRow_map hf]
      | some b => simp [mapTab_cons, insRow_map hf, ih]

/-- A strictly monotone map of the alphabet commutes with Schensted insertion of a word. -/
lemma RS_map (w : List σ) : RS (w.map f) = mapTab f (RS w) := by
  suffices h : ∀ (w : List σ) (P : List (List σ)),
      (w.map f).foldl insTab (mapTab f P) = mapTab f (w.foldl insTab P) by
    simpa [RS, mapTab] using h w []
  intro w
  induction w with
  | nil => simp
  | cons x w ih => intro P; simp only [List.map_cons, List.foldl_cons, insTab_mapTab hf, ih]

end MapRS

end Young
