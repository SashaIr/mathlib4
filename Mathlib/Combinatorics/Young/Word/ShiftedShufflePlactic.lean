/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.Plactic.Map
public import Mathlib.Combinatorics.Young.Plactic.Restrict
public import Mathlib.Combinatorics.Young.Plactic.RestrictGe
public import Mathlib.Combinatorics.Young.Word.ShiftedShuffle

/-!
# Schützenberger's theorem: the shifted shuffle is compatible with the plactic congruence

A Lean 4 port of `shift_plactcongr` and `Schutzenberger_shuffle_plact` in
`theories/LRrule/shuffle.v` of [Coq-Combi](https://github.com/math-comp/Coq-Combi).

If `w₁` is a shifted shuffle of a standard word `u₁` with a word `v₁`, and `w₂` is Knuth
equivalent to `w₁`, then `w₂` is again a shifted shuffle, of two words respectively Knuth
equivalent to `u₁` and `v₁`.  In other words, the shifted shuffle of two plactic classes is
a union of plactic classes; this is the statement underlying the Littlewood–Richardson rule
for the free Schur functions.

## Main results

* `Young.placticEquiv_shiftn_iff` : two words are Knuth equivalent if and only if their
  shifts are (Coq `shift_plactcongr`).
* `Young.placticEquiv_sfilterleq` : the large letters of Knuth equivalent words, shifted
  down, are Knuth equivalent.
* `Young.exists_placticEquiv_mem_shsh` : **Schützenberger's theorem** (Coq
  `Schutzenberger_shuffle_plact`).
-/

@[expose] public section

namespace Young

open List

variable {u v u₁ v₁ w₁ w₂ : List ℕ} {n : ℕ}

/-! ### Shifting the letters -/

/-- Shifting all the letters of two Knuth equivalent words keeps them Knuth equivalent. -/
lemma placticEquiv_shiftn (n : ℕ) (h : PlacticEquiv u v) :
    PlacticEquiv (shiftn n u) (shiftn n v) :=
  placticEquiv_map_of_strictMono (fun _ _ hab => Nat.add_lt_add_left hab n) h

/-- Two words are Knuth equivalent if and only if their shifts by `n` are
(Coq `shift_plactcongr`). -/
theorem placticEquiv_shiftn_iff (n : ℕ) :
    PlacticEquiv (shiftn n u) (shiftn n v) ↔ PlacticEquiv u v := by
  refine ⟨fun h => ?_, placticEquiv_shiftn n⟩
  have hmono : ∀ ⦃x : ℕ⦄, x ∈ {x : ℕ | n ≤ x} → ∀ ⦃y : ℕ⦄, y ∈ {x : ℕ | n ≤ x} →
      x < y → x - n < y - n := by
    intro x hx y hy hxy
    simp only [Set.mem_ofPred_eq] at hx hy
    omega
  have hmap := placticEquiv_map_of_strictMonoOn (F := (· - n)) hmono h
    (fun x hx => by simpa using le_of_mem_shiftn hx)
  simpa [shiftn, List.map_map, Function.comp_def] using hmap

/-- The letters `≥ n` of two Knuth equivalent words, shifted down by `n`, are Knuth
equivalent. -/
theorem placticEquiv_sfilterleq (n : ℕ) (h : PlacticEquiv u v) :
    PlacticEquiv (sfilterleq n u) (sfilterleq n v) := by
  have hupper : ∀ x y : ℕ, x ≤ y → decide (n ≤ x) → decide (n ≤ y) := by
    intro x y hxy hx
    simp only [decide_eq_true_eq] at hx ⊢
    omega
  have hfilter := placticEquiv_filter_of_isUpperSet hupper h
  have hmono : ∀ ⦃x : ℕ⦄, x ∈ {x : ℕ | n ≤ x} → ∀ ⦃y : ℕ⦄, y ∈ {x : ℕ | n ≤ x} →
      x < y → x - n < y - n := by
    intro x hx y hy hxy
    simp only [Set.mem_ofPred_eq] at hx hy
    omega
  exact placticEquiv_map_of_strictMonoOn (F := (· - n)) hmono hfilter
    (fun x hx => by simpa using (List.mem_filter.1 hx).2)

/-! ### Schützenberger's theorem -/

/-- **Schützenberger's theorem** (Coq `Schutzenberger_shuffle_plact`): if `w₁` is a shifted
shuffle of `u₁` and `v₁`, where all the letters of `u₁` are smaller than its length, and if
`w₂` is Knuth equivalent to `w₁`, then `w₂` is a shifted shuffle of two words respectively
Knuth equivalent to `u₁` and `v₁`. -/
theorem exists_placticEquiv_mem_shsh (hu₁ : ∀ x ∈ u₁, x < u₁.length)
    (hw : w₁ ∈ shsh u₁ v₁) (hpl : PlacticEquiv w₁ w₂) :
    ∃ u₂ v₂, PlacticEquiv u₁ u₂ ∧ PlacticEquiv v₁ v₂ ∧ w₂ ∈ shsh u₂ v₂ := by
  obtain ⟨hf, hs⟩ := (mem_shsh hu₁).1 hw
  set u₂ := w₂.filter (fun x => decide (x < u₁.length)) with hu₂
  have hplu : PlacticEquiv u₁ u₂ := by
    have := placticEquiv_ltFilter (N := u₁.length) hpl
    simp only [ltFilter] at this
    rwa [hf] at this
  have hplv : PlacticEquiv v₁ (sfilterleq u₁.length w₂) := by
    have := placticEquiv_sfilterleq u₁.length hpl
    rwa [hs] at this
  refine ⟨u₂, sfilterleq u₁.length w₂, hplu, hplv, ?_⟩
  have hperm : u₁.Perm u₂ := hplu.perm
  have hlen : u₂.length = u₁.length := hperm.length_eq.symm
  have hu₂mem : ∀ x ∈ u₂, x < u₂.length := by
    intro x hx
    rw [hlen]
    exact hu₁ x (hperm.mem_iff.2 hx)
  rw [mem_shsh hu₂mem, hlen]
  exact ⟨rfl, rfl⟩

end Young
