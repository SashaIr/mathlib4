/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.Crystal.Basic
public import Mathlib.Combinatorics.Young.Plactic.Basic

/-!
# The crystal operators and the plactic congruence

The crystal operators of `Mathlib.Combinatorics.Young.Crystal.Basic` are compatible with
Knuth equivalence: Knuth equivalent words have the same numbers of unmatched letters, and the words
obtained by applying a raising operator to two Knuth equivalent words are again Knuth equivalent.

The proof is the usual one: by the tensor rule, everything reduces to the three letter
words appearing in the two Knuth transformations.

## Main results

* `Young.crystalEps_of_placticEquiv`, `Young.crystalPhi_of_placticEquiv` : the numbers of
  unmatched letters are plactic invariants.
* `Young.crystalE_of_placticEquiv` : the raising operator is defined on a word iff it is
  defined on any Knuth equivalent word, and the results are Knuth equivalent.
-/

@[expose] public section

namespace Young

open List

/-! ### Words without the letter `i + 1` -/

lemma crystalPhi_eq_zero_of_notMem {i : ℕ} {w : List ℕ} (h : i + 1 ∉ w) :
    crystalPhi i w = 0 := by
  induction w with
  | nil => simp
  | cons x w ih =>
    have hx : x ≠ i + 1 := fun hc => h (by simp [hc])
    rw [crystalPhi_cons_of_ne hx]
    exact ih fun hc => h (List.mem_cons_of_mem _ hc)

lemma crystalE_eq_none_of_notMem {i : ℕ} {w : List ℕ} (h : i + 1 ∉ w) :
    crystalE i w = none :=
  (crystalE_eq_none_iff i w).2 (crystalPhi_eq_zero_of_notMem h)

lemma crystalEps_eq_count_of_notMem {i : ℕ} {w : List ℕ} (h : i + 1 ∉ w) :
    crystalEps i w = w.count i := by
  have := crystalPhi_add_count i w
  rw [crystalPhi_eq_zero_of_notMem h, List.count_eq_zero_of_not_mem h] at this
  omega

/-! ### Elementary Knuth transformations on three letters -/

lemma placticEquiv_ac {x y z : ℕ} (hxy : x ≤ y) (hyz : y < z) :
    PlacticEquiv [x, z, y] [z, x, y] := by
  simpa using (PlacticStep.knuthAC hxy hyz [] []).plactic

lemma placticEquiv_ca {x y z : ℕ} (hxy : x < y) (hyz : y ≤ z) :
    PlacticEquiv [y, x, z] [y, z, x] := by
  simpa using (PlacticStep.knuthCA hxy hyz [] []).plactic

/-! ### The compatibility relation -/

/-- Two words are `CrystalRel i`-related when they are Knuth equivalent, have the same
numbers of unmatched letters `i` and `i + 1`, and the raising operator `crystalE i` sends
them to Knuth equivalent words. -/
def CrystalRel (i : ℕ) (u v : List ℕ) : Prop :=
  PlacticEquiv u v ∧ crystalEps i u = crystalEps i v ∧ crystalPhi i u = crystalPhi i v ∧
    ∀ u', crystalE i u = some u' → ∃ v', crystalE i v = some v' ∧ PlacticEquiv u' v'

lemma CrystalRel.refl (i : ℕ) (u : List ℕ) : CrystalRel i u u :=
  ⟨PlacticEquiv.refl u, rfl, rfl, fun u' h => ⟨u', h, PlacticEquiv.refl u'⟩⟩

lemma CrystalRel.symm {i : ℕ} {u v : List ℕ} (h : CrystalRel i u v) : CrystalRel i v u := by
  obtain ⟨hpl, heps, hphi, he⟩ := h
  refine ⟨hpl.symm, heps.symm, hphi.symm, fun v' hv' => ?_⟩
  have hu : (crystalE i u).isSome := by
    rw [crystalE_isSome_iff, hphi, ← crystalE_isSome_iff]
    simp [hv']
  obtain ⟨u', hu'⟩ := Option.isSome_iff_exists.1 hu
  obtain ⟨v'', hv'', hequiv⟩ := he u' hu'
  rw [hv'] at hv''
  have hvv : v' = v'' := Option.some_inj.1 hv''
  subst hvv
  exact ⟨u', hu', hequiv.symm⟩

lemma CrystalRel.trans {i : ℕ} {u v w : List ℕ} (h1 : CrystalRel i u v)
    (h2 : CrystalRel i v w) : CrystalRel i u w := by
  obtain ⟨hpl1, heps1, hphi1, he1⟩ := h1
  obtain ⟨hpl2, heps2, hphi2, he2⟩ := h2
  refine ⟨hpl1.trans hpl2, heps1.trans heps2, hphi1.trans hphi2, fun u' hu' => ?_⟩
  obtain ⟨v', hv', h1'⟩ := he1 u' hu'
  obtain ⟨w', hw', h2'⟩ := he2 v' hv'
  exact ⟨w', hw', h1'.trans h2'⟩

lemma CrystalRel.append_left {i : ℕ} {u v : List ℕ} (h : CrystalRel i u v) (c : List ℕ) :
    CrystalRel i (c ++ u) (c ++ v) := by
  obtain ⟨hpl, heps, hphi, he⟩ := h
  refine ⟨hpl.append_left c, by simp only [crystalEps_append, heps],
    by simp only [crystalPhi_append, heps, hphi], fun u' hu' => ?_⟩
  rw [crystalE_append] at hu' ⊢
  rw [heps] at hu'
  by_cases hc : crystalEps i v < crystalPhi i c
  · rw [ite_eq_left hc] at hu' ⊢
    obtain ⟨c', hc', rfl⟩ := Option.map_eq_some_iff.1 hu'
    exact ⟨c' ++ v, by rw [hc']; rfl, hpl.append_left c'⟩
  · rw [ite_eq_right hc] at hu' ⊢
    obtain ⟨u0, hu0, rfl⟩ := Option.map_eq_some_iff.1 hu'
    obtain ⟨v0, hv0, hequiv⟩ := he u0 hu0
    exact ⟨c ++ v0, by rw [hv0]; rfl, hequiv.append_left c⟩

lemma CrystalRel.append_right {i : ℕ} {u v : List ℕ} (h : CrystalRel i u v) (d : List ℕ) :
    CrystalRel i (u ++ d) (v ++ d) := by
  obtain ⟨hpl, heps, hphi, he⟩ := h
  refine ⟨hpl.append_right d, by simp only [crystalEps_append, heps, hphi],
    by simp only [crystalPhi_append, hphi], fun u' hu' => ?_⟩
  rw [crystalE_append] at hu' ⊢
  rw [hphi] at hu'
  by_cases hc : crystalEps i d < crystalPhi i v
  · rw [ite_eq_left hc] at hu' ⊢
    obtain ⟨u0, hu0, rfl⟩ := Option.map_eq_some_iff.1 hu'
    obtain ⟨v0, hv0, hequiv⟩ := he u0 hu0
    exact ⟨v0 ++ d, by rw [hv0]; rfl, hequiv.append_right d⟩
  · rw [ite_eq_right hc] at hu' ⊢
    obtain ⟨d', hd', rfl⟩ := Option.map_eq_some_iff.1 hu'
    exact ⟨v ++ d', by rw [hd']; rfl, hpl.append_right d'⟩

/-- Two Knuth equivalent words which do not contain the letter `i + 1` are related. -/
lemma crystalRel_of_notMem {i : ℕ} {u v : List ℕ} (hpl : PlacticEquiv u v) (hperm : u.Perm v)
    (hu : i + 1 ∉ u) (hv : i + 1 ∉ v) : CrystalRel i u v := by
  refine ⟨hpl, ?_, ?_, ?_⟩
  · rw [crystalEps_eq_count_of_notMem hu, crystalEps_eq_count_of_notMem hv, hperm.count_eq]
  · rw [crystalPhi_eq_zero_of_notMem hu, crystalPhi_eq_zero_of_notMem hv]
  · intro u' h
    rw [crystalE_eq_none_of_notMem hu] at h
    exact absurd h (by simp)

/-! ### The three letter Knuth transformations -/

lemma crystalEps_ac (i : ℕ) {x y z : ℕ} (hxy : x ≤ y) (hyz : y < z) :
    crystalEps i [x, z, y] = crystalEps i [z, x, y] := by
  simp only [crystalEps]
  split_ifs <;> omega

lemma crystalPhi_ac (i : ℕ) {x y z : ℕ} (hxy : x ≤ y) (hyz : y < z) :
    crystalPhi i [x, z, y] = crystalPhi i [z, x, y] := by
  simp only [crystalPhi, crystalEps]
  split_ifs <;>
    simp only [and_true, and_false, not_false_iff, Nat.reduceSub, Nat.reduceAdd] at * <;> omega

lemma crystalEps_ca (i : ℕ) {x y z : ℕ} (hxy : x < y) (hyz : y ≤ z) :
    crystalEps i [y, x, z] = crystalEps i [y, z, x] := by
  simp only [crystalEps]
  split_ifs <;> omega

lemma crystalPhi_ca (i : ℕ) {x y z : ℕ} (hxy : x < y) (hyz : y ≤ z) :
    crystalPhi i [y, x, z] = crystalPhi i [y, z, x] := by
  simp only [crystalPhi, crystalEps]
  split_ifs <;>
    simp only [and_true, and_false, not_false_iff, Nat.reduceSub, Nat.reduceAdd] at * <;> omega

lemma crystalE_ac {i x y z : ℕ} (hxy : x ≤ y) (hyz : y < z) {u' : List ℕ}
    (h : crystalE i [x, z, y] = some u') :
    ∃ v', crystalE i [z, x, y] = some v' ∧ PlacticEquiv u' v' := by
  by_cases hz1 : z = i + 1
  · subst hz1
    by_cases hy0 : y = i
    · subst hy0
      rw [show crystalE y [x, y + 1, y] = none by
        simp [crystalE_cons, crystalEps, show x ≠ y + 1 by omega]] at h
      simp at h
    · have hy1 : y < i := by omega
      rw [show crystalE i [x, i + 1, y] = some [x, i, y] by
        simp [crystalE_cons, crystalEps, show x ≠ i + 1 by omega, show y ≠ i by omega,
          show y ≠ i + 1 by omega]] at h
      rw [← Option.some_inj.1 h]
      exact ⟨[i, x, y], by
        simp [crystalE_cons, crystalEps, show x ≠ i by omega, show x ≠ i + 1 by omega,
          show y ≠ i by omega, show y ≠ i + 1 by omega],
        placticEquiv_ac hxy hy1⟩
  · by_cases hy1 : y = i + 1
    · subst hy1
      have hz2 : i + 1 < z := by omega
      by_cases hx1 : x = i + 1
      · subst hx1
        rw [show crystalE i [i + 1, z, i + 1] = some [i, z, i + 1] by
          simp [crystalE_cons, crystalEps, show z ≠ i by omega, show z ≠ i + 1 by omega]] at h
        rw [← Option.some_inj.1 h]
        exact ⟨[z, i, i + 1], by
          simp [crystalE_cons, crystalEps, show z ≠ i + 1 by omega],
          placticEquiv_ac (by omega) hz2⟩
      · have hxi : x ≤ i := by omega
        rw [show crystalE i [x, z, i + 1] = some [x, z, i] by
          simp [crystalE_cons, crystalEps, show z ≠ i + 1 by omega,
            show x ≠ i + 1 by omega]] at h
        rw [← Option.some_inj.1 h]
        exact ⟨[z, x, i], by
          simp [crystalE_cons, crystalEps, show z ≠ i + 1 by omega,
            show x ≠ i + 1 by omega],
          placticEquiv_ac hxi (by omega)⟩
    · by_cases hx1 : x = i + 1
      · subst hx1
        have hy2 : i + 1 < y := by omega
        rw [show crystalE i [i + 1, z, y] = some [i, z, y] by
          simp [crystalE_cons, crystalEps, show z ≠ i by omega, show z ≠ i + 1 by omega,
            show y ≠ i by omega, show y ≠ i + 1 by omega]] at h
        rw [← Option.some_inj.1 h]
        exact ⟨[z, i, y], by
          simp [crystalE_cons, crystalEps, show z ≠ i + 1 by omega,
            show y ≠ i by omega, show y ≠ i + 1 by omega],
          placticEquiv_ac (by omega) hyz⟩
      · rw [crystalE_eq_none_of_notMem (by simp; omega)] at h
        simp at h

lemma crystalE_ca {i x y z : ℕ} (hxy : x < y) (hyz : y ≤ z) {u' : List ℕ}
    (h : crystalE i [y, x, z] = some u') :
    ∃ v', crystalE i [y, z, x] = some v' ∧ PlacticEquiv u' v' := by
  by_cases hx1 : x = i + 1
  · subst hx1
    have hy2 : i + 1 < y := hxy
    rw [show crystalE i [y, i + 1, z] = some [y, i, z] by
      simp [crystalE_cons, crystalEps, show y ≠ i + 1 by omega, show z ≠ i by omega,
        show z ≠ i + 1 by omega]] at h
    rw [← Option.some_inj.1 h]
    exact ⟨[y, z, i], by
      simp [crystalE_cons, crystalEps, show y ≠ i + 1 by omega, show z ≠ i by omega,
        show z ≠ i + 1 by omega],
      placticEquiv_ca (by omega) hyz⟩
  · by_cases hy1 : y = i + 1
    · subst hy1
      by_cases hz1 : z = i + 1
      · subst hz1
        by_cases hx0 : x = i
        · subst hx0
          rw [show crystalE x [x + 1, x, x + 1] = some [x + 1, x, x] by
            simp [crystalE_cons, crystalEps]] at h
          rw [← Option.some_inj.1 h]
          exact ⟨[x, x + 1, x], by simp [crystalE_cons, crystalEps],
            (placticEquiv_ac (le_refl x) (by omega)).symm⟩
        · have hxi : x < i := by omega
          rw [show crystalE i [i + 1, x, i + 1] = some [i, x, i + 1] by
            simp [crystalE_cons, crystalEps, show x ≠ i by omega, show x ≠ i + 1 by omega]] at h
          rw [← Option.some_inj.1 h]
          exact ⟨[i, i + 1, x], by
            simp [crystalE_cons, crystalEps, show x ≠ i by omega, show x ≠ i + 1 by omega],
            placticEquiv_ca hxi (by omega)⟩
      · have hz2 : i + 1 < z := by omega
        by_cases hx0 : x = i
        · subst hx0
          rw [show crystalE x [x + 1, x, z] = none by
            simp [crystalE_cons, crystalEps, show z ≠ x by omega, show z ≠ x + 1 by omega]] at h
          simp at h
        · have hxi : x < i := by omega
          rw [show crystalE i [i + 1, x, z] = some [i, x, z] by
            simp [crystalE_cons, crystalEps, show x ≠ i by omega, show x ≠ i + 1 by omega,
              show z ≠ i by omega, show z ≠ i + 1 by omega]] at h
          rw [← Option.some_inj.1 h]
          exact ⟨[i, z, x], by
            simp [crystalE_cons, crystalEps, show x ≠ i by omega, show x ≠ i + 1 by omega,
              show z ≠ i by omega, show z ≠ i + 1 by omega],
            placticEquiv_ca hxi (by omega)⟩
    · by_cases hz1 : z = i + 1
      · subst hz1
        by_cases hy0 : y = i
        · subst hy0
          rw [show crystalE y [y, x, y + 1] = some [y, x, y] by
            simp [crystalE_cons, crystalEps, show x ≠ y + 1 by omega]] at h
          rw [← Option.some_inj.1 h]
          exact ⟨[y, y, x], by
            simp [crystalE_cons, crystalEps, show x ≠ y by omega, show x ≠ y + 1 by omega],
            placticEquiv_ca hxy (le_refl y)⟩
        · have hyi : y < i := by omega
          rw [show crystalE i [y, x, i + 1] = some [y, x, i] by
            simp [crystalE_cons, crystalEps, show x ≠ i + 1 by omega,
              show y ≠ i + 1 by omega]] at h
          rw [← Option.some_inj.1 h]
          exact ⟨[y, i, x], by
            simp [crystalE_cons, crystalEps, show x ≠ i by omega, show x ≠ i + 1 by omega,
              show y ≠ i + 1 by omega],
            placticEquiv_ca hxy (by omega)⟩
      · rw [crystalE_eq_none_of_notMem (by simp; omega)] at h
        simp at h

lemma crystalRel_ac (i : ℕ) {x y z : ℕ} (hxy : x ≤ y) (hyz : y < z) :
    CrystalRel i [x, z, y] [z, x, y] :=
  ⟨placticEquiv_ac hxy hyz, crystalEps_ac i hxy hyz, crystalPhi_ac i hxy hyz,
    fun _ h => crystalE_ac hxy hyz h⟩

lemma crystalRel_ca (i : ℕ) {x y z : ℕ} (hxy : x < y) (hyz : y ≤ z) :
    CrystalRel i [y, x, z] [y, z, x] :=
  ⟨placticEquiv_ca hxy hyz, crystalEps_ca i hxy hyz, crystalPhi_ca i hxy hyz,
    fun _ h => crystalE_ca hxy hyz h⟩

/-! ### Compatibility with the plactic congruence -/

lemma crystalRel_of_placticStep (i : ℕ) {u v : List ℕ} (h : PlacticStep u v) :
    CrystalRel i u v := by
  cases h with
  | knuthAC hxy hyz a b =>
    simpa using ((crystalRel_ac i hxy hyz).append_right b).append_left a
  | knuthCA hxy hyz a b =>
    simpa using ((crystalRel_ca i hxy hyz).append_right b).append_left a

theorem crystalRel_of_placticEquiv (i : ℕ) {u v : List ℕ} (h : PlacticEquiv u v) :
    CrystalRel i u v := by
  induction h with
  | rel a b hab => exact crystalRel_of_placticStep i hab
  | refl a => exact CrystalRel.refl i a
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2

/-- The number of unmatched letters `i` is a plactic invariant. -/
theorem crystalEps_of_placticEquiv (i : ℕ) {u v : List ℕ} (h : PlacticEquiv u v) :
    crystalEps i u = crystalEps i v := (crystalRel_of_placticEquiv i h).2.1

/-- The number of unmatched letters `i + 1` is a plactic invariant. -/
theorem crystalPhi_of_placticEquiv (i : ℕ) {u v : List ℕ} (h : PlacticEquiv u v) :
    crystalPhi i u = crystalPhi i v := (crystalRel_of_placticEquiv i h).2.2.1

/-- The raising operator sends Knuth equivalent words to Knuth equivalent words. -/
theorem crystalE_of_placticEquiv (i : ℕ) {u v u' : List ℕ} (h : PlacticEquiv u v)
    (hu : crystalE i u = some u') :
    ∃ v', crystalE i v = some v' ∧ PlacticEquiv u' v' :=
  (crystalRel_of_placticEquiv i h).2.2.2 u' hu

end Young
