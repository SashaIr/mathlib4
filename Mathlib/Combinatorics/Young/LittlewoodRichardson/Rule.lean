/-
Copyright (c) 2026 Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/
import Mathlib.Data.Set.Card
import Mathlib.Combinatorics.Young.Crystal.RobinsonSchensted

/-!
# The Littlewood–Richardson rule: the combinatorial statement

Following the crystal (Lascoux–Schützenberger) proof of the Littlewood–Richardson rule, we
show here that for two fixed shapes `lam` and `mu`, the number of pairs `(S, T)` of
tableaux of shapes `lam` and `mu` whose plactic product `RS (toWord S ++ toWord T)` is a
given tableau `V` only depends on the shape of `V`.  This common value is the
Littlewood–Richardson coefficient `List.lrCoeff lam mu nu`, defined as the number of such
pairs whose product is the superstandard tableau of shape `nu`.

The proof is the crystal one: the crystal operators act on pairs of tableaux
(`List.pairE` and `List.pairF`) compatibly with the plactic product, they preserve the
shapes of the two factors, and the crystal graph on tableaux of a fixed shape is connected
with the superstandard tableau as its highest weight element
(`List.reflTransGen_tabRaise_superTab`).

## Main definitions

* `List.lrPairs lam mu V` : the pairs of tableaux of shapes `lam` and `mu` with plactic
  product `V`.
* `List.pairE`, `List.pairF` : the crystal operators acting on pairs of tableaux.
* `List.lrCoeff lam mu nu` : the Littlewood–Richardson coefficient.

## Main results

* `List.ncard_lrPairs_eq_lrCoeff` : for any tableau `V`, the number of pairs of tableaux
  of shapes `lam` and `mu` with plactic product `V` is `lrCoeff lam mu (shape V)`.
* `List.lrCoeff_eq_ncard_lrTableaux` : the coefficient counts the tableaux of shape `lam`
  whose product with the superstandard tableau of shape `mu` is superstandard.
* `List.lrCoeff_nil_right` : `c^lam_{lam, ∅} = 1`.
-/

namespace List

open List

/-! ### Preliminaries -/

lemma length_crystalE {i : ℕ} {w w' : List ℕ} (h : crystalE i w = some w') :
    w'.length = w.length := by
  obtain ⟨j, hj, -, rfl⟩ := crystalE_eq_set h
  simp

lemma length_crystalF {i : ℕ} {w w' : List ℕ} (h : crystalF i w = some w') :
    w'.length = w.length := by
  obtain ⟨j, hj, -, rfl⟩ := crystalF_eq_set h
  simp

/-- Two pairs of tableaux with the same concatenated reading word and the same first shape
are equal. -/
lemma eq_of_toWord_append_eq {A B C D : List (List ℕ)} (hA : IsTableau A) (hB : IsTableau B)
    (hC : IsTableau C) (hD : IsTableau D) (hsh : shape A = shape C)
    (h : toWord A ++ toWord B = toWord C ++ toWord D) : A = C ∧ B = D := by
  have hlen : (toWord A).length = (toWord C).length := by
    rw [length_toWord, length_toWord, sizeTab, sizeTab, hsh]
  obtain ⟨h1, h2⟩ := List.append_inj h hlen
  exact ⟨by rw [← RS_toWord hA, h1, RS_toWord hC], by rw [← RS_toWord hB, h2, RS_toWord hD]⟩

/-! ### Pairs of tableaux with a given plactic product -/

/-- The set of pairs of tableaux of shapes `lam` and `mu` whose plactic product is `V`. -/
def lrPairs (lam mu : List ℕ) (V : List (List ℕ)) : Set (List (List ℕ) × List (List ℕ)) :=
  {p | IsTableau p.1 ∧ shape p.1 = lam ∧ IsTableau p.2 ∧ shape p.2 = mu ∧
    RS (toWord p.1 ++ toWord p.2) = V}

/-- The raising operator acting on a pair of tableaux: it raises the concatenated reading
word and cuts the result at the same place. -/
noncomputable def pairE (i : ℕ) (p : List (List ℕ) × List (List ℕ)) :
    List (List ℕ) × List (List ℕ) :=
  ((crystalE i (toWord p.1 ++ toWord p.2)).map
    (fun w => (RS (w.take (toWord p.1).length), RS (w.drop (toWord p.1).length)))).getD p

/-- The lowering operator acting on a pair of tableaux. -/
noncomputable def pairF (i : ℕ) (p : List (List ℕ) × List (List ℕ)) :
    List (List ℕ) × List (List ℕ) :=
  ((crystalF i (toWord p.1 ++ toWord p.2)).map
    (fun w => (RS (w.take (toWord p.1).length), RS (w.drop (toWord p.1).length)))).getD p

lemma pairE_eq {i : ℕ} {S T : List (List ℕ)} (hS : IsTableau S) (hT : IsTableau T) {w : List ℕ}
    (h : crystalE i (toWord S ++ toWord T) = some w) :
    ∃ S' T', pairE i (S, T) = (S', T') ∧ IsTableau S' ∧ IsTableau T' ∧
      shape S' = shape S ∧ shape T' = shape T ∧ toWord S' ++ toWord T' = w := by
  rw [crystalE_append] at h
  by_cases hcond : crystalEps i (toWord T) < crystalPhi i (toWord S)
  · rw [if_pos hcond] at h
    obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨S', hword, hS', hshape⟩ := exists_isTableau_crystalE hS hu
    refine ⟨S', T, ?_, hS', hT, hshape, rfl, by rw [hword]⟩
    have hlen : u.length = (toWord S).length := length_crystalE hu
    have h1 : (u ++ toWord T).take (toWord S).length = u := by rw [← hlen, List.take_left]
    have h2 : (u ++ toWord T).drop (toWord S).length = toWord T := by rw [← hlen, List.drop_left]
    rw [pairE]
    simp only [crystalE_append, if_pos hcond, hu, Option.map_some, Option.getD_some, h1, h2]
    rw [← hword, RS_toWord hS', RS_toWord hT]
  · rw [if_neg hcond] at h
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨T', hword, hT', hshape⟩ := exists_isTableau_crystalE hT hv
    refine ⟨S, T', ?_, hS, hT', rfl, hshape, by rw [hword]⟩
    have h1 : (toWord S ++ v).take (toWord S).length = toWord S := List.take_left
    have h2 : (toWord S ++ v).drop (toWord S).length = v := List.drop_left
    rw [pairE]
    simp only [crystalE_append, if_neg hcond, hv, Option.map_some, Option.getD_some, h1, h2]
    rw [← hword, RS_toWord hS, RS_toWord hT']

lemma pairF_eq {i : ℕ} {S T : List (List ℕ)} (hS : IsTableau S) (hT : IsTableau T) {w : List ℕ}
    (h : crystalF i (toWord S ++ toWord T) = some w) :
    ∃ S' T', pairF i (S, T) = (S', T') ∧ IsTableau S' ∧ IsTableau T' ∧
      shape S' = shape S ∧ shape T' = shape T ∧ toWord S' ++ toWord T' = w := by
  rw [crystalF_append] at h
  by_cases hcond : crystalPhi i (toWord S) < crystalEps i (toWord T)
  · rw [if_pos hcond] at h
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨T', hword, hT', hshape⟩ := exists_isTableau_crystalF hT hv
    refine ⟨S, T', ?_, hS, hT', rfl, hshape, by rw [hword]⟩
    have h1 : (toWord S ++ v).take (toWord S).length = toWord S := List.take_left
    have h2 : (toWord S ++ v).drop (toWord S).length = v := List.drop_left
    rw [pairF]
    simp only [crystalF_append, if_pos hcond, hv, Option.map_some, Option.getD_some, h1, h2]
    rw [← hword, RS_toWord hS, RS_toWord hT']
  · rw [if_neg hcond] at h
    obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨S', hword, hS', hshape⟩ := exists_isTableau_crystalF hS hu
    refine ⟨S', T, ?_, hS', hT, hshape, rfl, by rw [hword]⟩
    have hlen : u.length = (toWord S).length := length_crystalF hu
    have h1 : (u ++ toWord T).take (toWord S).length = u := by rw [← hlen, List.take_left]
    have h2 : (u ++ toWord T).drop (toWord S).length = toWord T := by rw [← hlen, List.drop_left]
    rw [pairF]
    simp only [crystalF_append, if_neg hcond, hu, Option.map_some, Option.getD_some, h1, h2]
    rw [← hword, RS_toWord hS', RS_toWord hT]

/-! ### The crystal operators on pairs of tableaux with a given plactic product -/

lemma pairE_mem_lrPairs {i : ℕ} {lam mu : List ℕ} {V V' : List (List ℕ)} (hV' : IsTableau V')
    (hstep : crystalE i (toWord V) = some (toWord V')) {p : List (List ℕ) × List (List ℕ)}
    (hp : p ∈ lrPairs lam mu V) :
    pairE i p ∈ lrPairs lam mu V' ∧
      crystalE i (toWord p.1 ++ toWord p.2) =
        some (toWord (pairE i p).1 ++ toWord (pairE i p).2) := by
  obtain ⟨S, T⟩ := p
  obtain ⟨hS, hshS, hT, hshT, hRS⟩ := hp
  have hV : IsTableau V := hRS ▸ isTableau_RS _
  have hpl : PlacticEquiv (toWord V) (toWord S ++ toWord T) :=
    placticEquiv_iff_RS_eq.2 (by rw [RS_toWord hV, hRS])
  obtain ⟨w, hw, hplw⟩ := crystalE_of_placticEquiv i hpl hstep
  have hRSw : RS w = V' := by rw [← RS_eq_of_placticEquiv hplw, RS_toWord hV']
  obtain ⟨S', T', hpair, hS', hT', hshS', hshT', hword⟩ := pairE_eq hS hT hw
  rw [hpair]
  refine ⟨⟨hS', by rw [hshS', hshS], hT', by rw [hshT', hshT], by rw [hword, hRSw]⟩, ?_⟩
  rw [hw, hword]

lemma pairF_mem_lrPairs {i : ℕ} {lam mu : List ℕ} {V V' : List (List ℕ)} (hV : IsTableau V)
    (hstep : crystalF i (toWord V') = some (toWord V)) {q : List (List ℕ) × List (List ℕ)}
    (hq : q ∈ lrPairs lam mu V') :
    pairF i q ∈ lrPairs lam mu V ∧
      crystalF i (toWord q.1 ++ toWord q.2) =
        some (toWord (pairF i q).1 ++ toWord (pairF i q).2) := by
  obtain ⟨S, T⟩ := q
  obtain ⟨hS, hshS, hT, hshT, hRS⟩ := hq
  have hV' : IsTableau V' := hRS ▸ isTableau_RS _
  have hpl : PlacticEquiv (toWord V') (toWord S ++ toWord T) :=
    placticEquiv_iff_RS_eq.2 (by rw [RS_toWord hV', hRS])
  obtain ⟨w, hw, hplw⟩ := crystalF_of_placticEquiv i hpl hstep
  have hRSw : RS w = V := by rw [← RS_eq_of_placticEquiv hplw, RS_toWord hV]
  obtain ⟨S', T', hpair, hS', hT', hshS', hshT', hword⟩ := pairF_eq hS hT hw
  rw [hpair]
  refine ⟨⟨hS', by rw [hshS', hshS], hT', by rw [hshT', hshT], by rw [hword, hRSw]⟩, ?_⟩
  rw [hw, hword]

/-- One step of the crystal action gives a bijection between the pairs of tableaux with
plactic product `V` and those with plactic product `V'`. -/
theorem bijOn_pairE {i : ℕ} {lam mu : List ℕ} {V V' : List (List ℕ)} (hV : IsTableau V)
    (hV' : IsTableau V') (hstep : crystalE i (toWord V) = some (toWord V')) :
    Set.BijOn (pairE i) (lrPairs lam mu V) (lrPairs lam mu V') := by
  have hstepF : crystalF i (toWord V') = some (toWord V) := crystalF_crystalE hstep
  refine ⟨fun p hp => (pairE_mem_lrPairs hV' hstep hp).1, ?_, ?_⟩
  · intro p hp q hq hpq
    obtain ⟨hpmem, hpw⟩ := pairE_mem_lrPairs hV' hstep hp
    obtain ⟨hqmem, hqw⟩ := pairE_mem_lrPairs hV' hstep hq
    rw [hpq] at hpw
    have hwords := crystalE_injective i hpw hqw
    obtain ⟨h1, h2⟩ := eq_of_toWord_append_eq hp.1 hp.2.2.1 hq.1 hq.2.2.1
      (by rw [hp.2.1, hq.2.1]) hwords
    exact Prod.ext h1 h2
  · intro q hq
    obtain ⟨hmem, hword⟩ := pairF_mem_lrPairs hV hstepF hq
    refine ⟨pairF i q, hmem, ?_⟩
    obtain ⟨hmem', hword'⟩ := pairE_mem_lrPairs hV' hstep hmem
    have hEq : crystalE i (toWord (pairF i q).1 ++ toWord (pairF i q).2) =
        some (toWord q.1 ++ toWord q.2) := crystalE_crystalF hword
    rw [hword'] at hEq
    obtain ⟨h1, h2⟩ := eq_of_toWord_append_eq hmem'.1 hmem'.2.2.1 hq.1 hq.2.2.1
      (by rw [hmem'.2.1, hq.2.1]) (Option.some_inj.1 hEq)
    exact Prod.ext h1 h2

theorem ncard_lrPairs_eq_of_tabRaise {lam mu : List ℕ} {V V' : List (List ℕ)}
    (h : TabRaise V V') : (lrPairs lam mu V).ncard = (lrPairs lam mu V').ncard := by
  obtain ⟨hV, hV', i, hstep⟩ := h
  have hbij : Set.BijOn (pairE i) (lrPairs lam mu V) (lrPairs lam mu V') :=
    bijOn_pairE hV hV' hstep
  rw [← hbij.image_eq, Set.InjOn.ncard_image hbij.injOn]

/-! ### The Littlewood–Richardson coefficients -/

/-- The Littlewood–Richardson coefficient `c^nu_{lam mu}` : the number of pairs of tableaux
of shapes `lam` and `mu` whose plactic product is the superstandard tableau of shape
`nu`. -/
noncomputable def lrCoeff (lam mu nu : List ℕ) : ℕ := (lrPairs lam mu (superTab nu)).ncard

/-- The number of pairs with a given plactic product is invariant along the crystal
graph. -/
theorem ncard_lrPairs_eq_of_reflTransGen {lam mu : List ℕ} {V W : List (List ℕ)}
    (h : Relation.ReflTransGen TabRaise V W) :
    (lrPairs lam mu V).ncard = (lrPairs lam mu W).ncard := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => rw [ih, ncard_lrPairs_eq_of_tabRaise hstep]

/-- **The Littlewood–Richardson rule**, combinatorial form: the number of pairs of tableaux
of shapes `lam` and `mu` whose plactic product is a given tableau `V` only depends on the
shape of `V`, and is the Littlewood–Richardson coefficient. -/
theorem ncard_lrPairs_eq_lrCoeff {lam mu : List ℕ} {V : List (List ℕ)} (hV : IsTableau V) :
    (lrPairs lam mu V).ncard = lrCoeff lam mu (shape V) :=
  ncard_lrPairs_eq_of_reflTransGen (reflTransGen_tabRaise_superTab (toWord V).sum V hV rfl)

/-! ### The Littlewood–Richardson coefficients count dominant tableaux -/

/-- The tableaux of shape `lam` whose plactic product with the superstandard tableau of
shape `mu` is the superstandard tableau of shape `nu`. -/
def lrTableaux (lam mu nu : List ℕ) : Set (List (List ℕ)) :=
  {S | IsTableau S ∧ shape S = lam ∧ RS (toWord S ++ toWord (superTab mu)) = superTab nu}

/-- In a pair of tableaux whose plactic product is superstandard, the second tableau is
itself superstandard, so that the Littlewood–Richardson coefficient counts the tableaux of
shape `lam` whose product with the superstandard tableau of shape `mu` is the superstandard
tableau of shape `nu`. -/
theorem lrCoeff_eq_ncard_lrTableaux {lam mu nu : List ℕ} (hmu : IsPart mu) (hnu : IsPart nu) :
    lrCoeff lam mu nu = (lrTableaux lam mu nu).ncard := by
  have hsuperNu : IsTableau (superTab nu) := isTableau_superTab hnu
  have hkey : ∀ p ∈ lrPairs lam mu (superTab nu), p.2 = superTab mu := by
    rintro ⟨S, T⟩ ⟨hS, hshS, hT, hshT, hRS⟩
    have hpl : PlacticEquiv (toWord S ++ toWord T) (toWord (superTab nu)) :=
      placticEquiv_iff_RS_eq.2 (by rw [hRS, RS_toWord hsuperNu])
    have hzero : ∀ i, crystalPhi i (toWord T) = 0 := by
      intro i
      have h1 := crystalPhi_of_placticEquiv i hpl
      rw [crystalPhi_toWord_superTab hnu i, crystalPhi_append] at h1
      omega
    have hsuper := eq_superTab_of_crystalPhi_eq_zero hT hzero
    rw [hsuper, hshT]
  have hbij : Set.BijOn Prod.fst (lrPairs lam mu (superTab nu)) (lrTableaux lam mu nu) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨S, T⟩ hp
      obtain ⟨hS, hshS, hT, hshT, hRS⟩ := hp
      exact ⟨hS, hshS, by rw [← hkey ⟨S, T⟩ ⟨hS, hshS, hT, hshT, hRS⟩]; exact hRS⟩
    · rintro ⟨S, T⟩ hp ⟨S', T'⟩ hq hST
      have h1 := hkey _ hp
      have h2 := hkey _ hq
      simp only at hST h1 h2
      exact Prod.ext hST (by rw [h1, h2])
    · rintro S ⟨hS, hshS, hRS⟩
      exact ⟨(S, superTab mu), ⟨hS, hshS, isTableau_superTab hmu, shape_superTab mu, hRS⟩, rfl⟩
  rw [lrCoeff, ← hbij.image_eq, Set.InjOn.ncard_image hbij.injOn]

/-! ### A degenerate case -/

/-- Multiplying by the empty shape does nothing: `c^lam_{lam, ∅} = 1`.  In particular the
Littlewood–Richardson coefficients are not all zero. -/
theorem lrCoeff_nil_right {lam : List ℕ} (hlam : IsPart lam) : lrCoeff lam [] lam = 1 := by
  have hset : lrPairs lam [] (superTab lam) = {(superTab lam, ([] : List (List ℕ)))} := by
    ext ⟨S, T⟩
    constructor
    · rintro ⟨hS, hshS, -, hshT, hRS⟩
      have hT : T = [] := List.map_eq_nil_iff.1 hshT
      subst hT
      rw [toWord_nil, List.append_nil, RS_toWord hS] at hRS
      exact Prod.ext hRS rfl
    · intro hmem
      simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      exact ⟨isTableau_superTab hlam, shape_superTab lam, isTableau_nil, rfl, by
        rw [toWord_nil, List.append_nil, RS_toWord (isTableau_superTab hlam)]⟩
  rw [lrCoeff, hset, Set.ncard_singleton]

end List
