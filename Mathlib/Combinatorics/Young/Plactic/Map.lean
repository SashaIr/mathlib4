/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.Plactic.Basic

/-!
# Knuth equivalence and increasing maps

Applying an increasing map to all the letters of a word preserves Knuth (plactic)
equivalence, since an elementary Knuth transformation only depends on the relative order of
its three letters.  This is the Lean 4 port of `plact_map_in_incr` in
`theories/LRrule/plactic.v` of [Coq-Combi](https://github.com/math-comp/Coq-Combi).

## Main results

* `List.placticEquiv_map_of_strictMonoOn` : Knuth equivalent words stay Knuth equivalent
  after applying a map which is strictly increasing on a set containing their letters.
* `List.placticEquiv_map_of_strictMono` : the same for a globally strictly increasing map.
-/

namespace List

variable {T T' : Type*} [LinearOrder T] [LinearOrder T']

/-- An elementary Knuth transformation is transported by a map which is strictly increasing
on a set containing the letters of the word. -/
lemma placticStep_map_of_strictMonoOn {S : Set T} {F : T → T'}
    (hF : ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x < y → F x < F y) {u v : List T}
    (hu : ∀ x ∈ u, x ∈ S) (h : PlacticStep u v) :
    PlacticStep (u.map F) (v.map F) := by
  have mono : ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≤ y → F x ≤ F y := by
    intro x hx y hy hxy
    rcases eq_or_lt_of_le hxy with rfl | hlt
    · exact le_refl _
    · exact (hF hx hy hlt).le
  cases h with
  | @knuthAC x y z hxy hyz a b =>
    have hx : x ∈ S := hu x (by simp)
    have hy : y ∈ S := hu y (by simp)
    have hz : z ∈ S := hu z (by simp)
    simpa using PlacticStep.knuthAC (mono hx hy hxy) (hF hy hz hyz) (a.map F) (b.map F)
  | @knuthCA x y z hxy hyz a b =>
    have hy : y ∈ S := hu y (by simp)
    have hx : x ∈ S := hu x (by simp)
    have hz : z ∈ S := hu z (by simp)
    simpa using PlacticStep.knuthCA (hF hx hy hxy) (mono hy hz hyz) (a.map F) (b.map F)

/-- Knuth equivalent words stay Knuth equivalent after applying a map which is strictly
increasing on a set containing their letters (Coq `plact_map_in_incr`). -/
theorem placticEquiv_map_of_strictMonoOn {S : Set T} {F : T → T'}
    (hF : ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x < y → F x < F y) {u v : List T}
    (h : PlacticEquiv u v) (hu : ∀ x ∈ u, x ∈ S) :
    PlacticEquiv (u.map F) (v.map F) := by
  induction h with
  | rel a b hab => exact (placticStep_map_of_strictMonoOn hF hu hab).plactic
  | refl a => exact PlacticEquiv.refl _
  | symm a b hab ih =>
    exact (ih fun x hx => hu x ((show PlacticEquiv a b from hab).perm.mem_iff.1 hx)).symm
  | trans a b c hab _ ih1 ih2 =>
    exact (ih1 hu).trans
      (ih2 fun x hx => hu x ((show PlacticEquiv a b from hab).perm.mem_iff.2 hx))

/-- Knuth equivalent words stay Knuth equivalent after applying a strictly increasing map. -/
theorem placticEquiv_map_of_strictMono {F : T → T'} (hF : StrictMono F) {u v : List T}
    (h : PlacticEquiv u v) : PlacticEquiv (u.map F) (v.map F) :=
  placticEquiv_map_of_strictMonoOn (S := Set.univ) (fun _ _ _ _ hxy => hF hxy) h
    fun _ _ => Set.mem_univ _

end List
