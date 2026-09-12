/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.Tableau.Kostka
public import Mathlib.Combinatorics.Young.Tableau.Map
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.Basic

/-!
# Schur polynomials and Kostka numbers

The coefficients of the Schur polynomial `s_μ` are Kostka numbers, so the results of
`Mathlib/Combinatorics/Young/Tableau/Kostka.lean` on Kostka numbers translate into statements
about `s_μ`: the monomial `x ^ d` occurs only if the shape `μ` dominates the content `d`, and the
monomial of content `μ` itself occurs exactly once.  In other words

`s_μ = m_μ + (terms of content strictly dominated by μ)`.

## Main definitions

## Main results

* `MvPolynomial.coeff_schurPoly_eq_zero_of_not_partdom` : the coefficient of `x ^ d` in `s_μ`
  vanishes unless `μ` dominates the content `d`.
* `MvPolynomial.coeff_schurPoly_self` : the coefficient of the monomial of content `μ` in
  `s_μ` is `1`.
-/

@[expose] public section

open Young

namespace MvPolynomial

open List MvPolynomial

/-! ### From tableaux over `Fin m` to tableaux over `ℕ` -/

variable {m : ℕ} {R : Type*} [CommSemiring R]

lemma isTableau_mapTab_val {P : List (List (Fin m))} (hP : IsTableau P) :
    IsTableau (mapTab (Fin.val : Fin m → ℕ) P) :=
  isTableau_mapTab Fin.val_strictMono hP

lemma count_map_val (l : List (Fin m)) (i : ℕ) :
    (l.map Fin.val).count i = if h : i < m then l.count ⟨i, h⟩ else 0 := by
  by_cases h : i < m
  · rw [dite_eq_left h]
    exact List.count_map_of_injective l Fin.val Fin.val_injective ⟨i, h⟩
  · rw [dite_eq_right h]
    refine List.count_eq_zero_of_not_mem ?_
    intro hmem
    obtain ⟨a, -, ha⟩ := List.mem_map.1 hmem
    exact h (ha ▸ a.2)

/-- The counts of the letters in the reading word of a tableau over `Fin m`, read off from
the content. -/
lemma count_toWord_map_val {P : List (List (Fin m))} {d : Fin m →₀ ℕ}
    (hd : (toWord P : Multiset (Fin m)) = Finsupp.toMultiset d) (i : ℕ) :
    ((toWord P).map Fin.val).count i = (List.ofFn fun j : Fin m => d j).getD i 0 := by
  have hcount : ∀ j : Fin m, (toWord P).count j = d j := by
    intro j
    have h : Multiset.count j (toWord P : Multiset (Fin m))
        = Multiset.count j (Finsupp.toMultiset d) := by rw [hd]
    simpa [Finsupp.count_toMultiset] using h
  rw [count_map_val]
  by_cases h : i < m
  · rw [dite_eq_left h, hcount, List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · rw [dite_eq_right h, List.getD_eq_default _ _ (by simpa using h)]

/-- The coefficient of `x ^ d` in the Schur polynomial of shape `μ` vanishes unless `μ`
dominates the content `d`. -/
theorem coeff_schurPoly_eq_zero_of_not_partdom (μ : List ℕ) (d : Fin m →₀ ℕ)
    (h : ¬ Partdom (List.ofFn fun i : Fin m => d i) μ) :
    (schurPoly (Fin m) R μ).coeff d = 0 := by
  classical
  rw [coeff_schurPoly]
  have hempty : IsEmpty
      {T : SSYT (Fin m) μ // (toWord T.1 : Multiset (Fin m)) = Finsupp.toMultiset d} := by
    constructor
    rintro ⟨T, hT⟩
    refine h ?_
    have ht := partdom_evalseq_toWord (isTableau_mapTab_val T.2.1)
    rw [shape_mapTab, T.2.2, toWord_mapTab] at ht
    intro k
    have hsum : ((List.ofFn fun i : Fin m => d i).take k).sum
        = ((evalseq ((toWord T.1).map Fin.val)).take k).sum := by
      rw [sum_take_eq_sum_range, sum_take_eq_sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [getD_evalseq, count_toWord_map_val hT i]
    rw [hsum]
    exact ht k
  rw [Nat.card_of_isEmpty, Nat.cast_zero]

/-- A tableau over `Fin m` has at most `m` rows. -/
lemma length_le_of_isTableau {P : List (List (Fin m))} (hP : IsTableau P) : P.length ≤ m := by
  by_contra hlt
  push Not at hlt
  have htab : IsTableau (mapTab (Fin.val : Fin m → ℕ) P) := isTableau_mapTab_val hP
  have hlen : (mapTab (Fin.val : Fin m → ℕ) P).length = P.length := by simp [mapTab]
  have hne : (mapTab (Fin.val : Fin m → ℕ) P).getD m [] ≠ [] := by
    intro hc
    have hpos : 0 < (shape (mapTab (Fin.val : Fin m → ℕ) P)).getD m 0 :=
      (isPart_shape htab).getD_pos (by simpa [shape, hlen] using hlt)
    rw [getD_shape, hc] at hpos
    simp at hpos
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne
  have hxm : m ≤ x := le_of_mem_getD_tableau htab m hx
  rw [getD_mapTab] at hx
  obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
  exact absurd a.2 (by omega)

/-- The Schur polynomial of a shape with more than `m` rows vanishes in `m` variables. -/
theorem schurPoly_eq_zero_of_lt_length {μ : List ℕ} (hlen : m < μ.length) :
    schurPoly (Fin m) R μ = 0 := by
  have : IsEmpty (SSYT (Fin m) μ) := by
    constructor
    rintro ⟨P, hP, hμ⟩
    have := length_le_of_isTableau hP
    have hlength : P.length = μ.length := by
      simpa [shape] using congrArg List.length hμ
    omega
  rw [schurPoly, Finset.univ_eq_empty, Finset.sum_empty]

/-! ### The coefficient of the monomial of content the shape -/

/-- The exponent vector recording the content `μ` over the alphabet `Fin m`. -/
noncomputable def shapeContent (m : ℕ) (μ : List ℕ) : Fin m →₀ ℕ :=
  Finsupp.onFinset Finset.univ (fun i : Fin m => μ.getD i 0) (fun _ _ => Finset.mem_univ _)

@[simp] lemma shapeContent_apply (μ : List ℕ) (i : Fin m) :
    shapeContent m μ i = μ.getD i 0 := rfl

/-- The superstandard tableau of shape `μ` over the alphabet `Fin m`: its `i`-th row
consists of `μ i` copies of the letter `i`. -/
def superTabFin (m : ℕ) (μ : List ℕ) (hlen : μ.length ≤ m) : List (List (Fin m)) :=
  List.ofFn fun j : Fin μ.length =>
    List.replicate (μ.getD j 0) (⟨j, lt_of_lt_of_le j.2 hlen⟩ : Fin m)

lemma mapTab_val_superTabFin (μ : List ℕ) (hlen : μ.length ≤ m) :
    mapTab (Fin.val : Fin m → ℕ) (superTabFin m μ hlen) = superTab μ := by
  have hlength : (superTab μ).length = μ.length := by
    simpa [shape] using congrArg List.length (shape_superTab μ)
  refine List.ext_getElem (by simp [superTabFin, mapTab, hlength]) fun j h1 h2 => ?_
  have hj : j < μ.length := by omega
  have hlhs : (mapTab (Fin.val : Fin m → ℕ) (superTabFin m μ hlen))[j]'h1
      = List.replicate (μ.getD j 0) j := by
    simp [mapTab, superTabFin, List.map_replicate, List.getElem?_eq_getElem hj]
  rw [hlhs, ← List.getD_eq_getElem _ _ h2, getD_superTab]

lemma isTableau_superTabFin {μ : List ℕ} (hμ : IsPart μ) (hlen : μ.length ≤ m) :
    IsTableau (superTabFin m μ hlen) :=
  isTableau_of_isTableau_mapTab Fin.val_strictMono
    (by rw [mapTab_val_superTabFin]; exact isTableau_superTab hμ)

lemma shape_superTabFin (μ : List ℕ) (hlen : μ.length ≤ m) :
    shape (superTabFin m μ hlen) = μ := by
  rw [← shape_mapTab (Fin.val : Fin m → ℕ), mapTab_val_superTabFin, shape_superTab]

lemma count_toWord_superTabFin (μ : List ℕ) (hlen : μ.length ≤ m) (j : Fin m) :
    (toWord (superTabFin m μ hlen)).count j = μ.getD j 0 := by
  have h := count_toWord_superTab μ (j : ℕ)
  rw [← mapTab_val_superTabFin μ hlen, toWord_mapTab, count_map_val, dite_eq_left j.2] at h
  simpa using h

/-- The coefficient of the monomial of content `μ` in the Schur polynomial of shape `μ`
is `1`: `s_μ = m_μ + (terms of content strictly dominated by μ)`. -/
theorem coeff_schurPoly_self {μ : List ℕ} (hμ : IsPart μ) (hlen : μ.length ≤ m) :
    (schurPoly (Fin m) R μ).coeff (shapeContent m μ) = 1 := by
  classical
  rw [coeff_schurPoly]
  have hgetD : ∀ i : ℕ, (List.ofFn fun j : Fin m => shapeContent m μ j).getD i 0
      = μ.getD i 0 := by
    intro i
    by_cases hi : i < m
    · rw [List.getD_eq_getElem _ _ (by simpa using hi)]
      simp
    · rw [List.getD_eq_default _ _ (by simpa using hi),
        List.getD_eq_default _ _ (by omega)]
  have hcontent : ∀ P : List (List (Fin m)),
      ((toWord P : Multiset (Fin m)) = Finsupp.toMultiset (shapeContent m μ))
        ↔ ∀ j : Fin m, (toWord P).count j = μ.getD j 0 := by
    intro P
    rw [Multiset.ext]
    constructor
    · intro h j
      simpa [Finsupp.count_toMultiset] using h j
    · intro h j
      simpa [Finsupp.count_toMultiset] using h j
  have hcard : Nat.card {T : SSYT (Fin m) μ //
      (toWord T.1 : Multiset (Fin m)) = Finsupp.toMultiset (shapeContent m μ)} = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨⟨superTabFin m μ hlen, isTableau_superTabFin hμ hlen, shape_superTabFin μ hlen⟩,
      (hcontent _).2 (count_toWord_superTabFin μ hlen)⟩, ?_⟩
    rintro ⟨T, hT⟩
    refine Subtype.ext (Subtype.ext ?_)
    have ht : IsTableau (mapTab (Fin.val : Fin m → ℕ) T.1) := isTableau_mapTab_val T.2.1
    have hshape : shape (mapTab (Fin.val : Fin m → ℕ) T.1) = μ := by
      rw [shape_mapTab, T.2.2]
    have hev : evalseq (toWord (mapTab (Fin.val : Fin m → ℕ) T.1)) = μ := by
      refine ext_getD_of_getLastD_ne_zero (getLastD_evalseq_ne_zero _) hμ.getLastD_ne_zero ?_
      intro i
      rw [getD_evalseq, toWord_mapTab, count_toWord_map_val hT i, hgetD i]
    have hsuper := eq_superTab_of_evalseq_eq ht (by rw [hev, hshape])
    rw [hshape] at hsuper
    refine mapTab_injective (f := (Fin.val : Fin m → ℕ)) Fin.val_injective ?_
    rw [hsuper, mapTab_val_superTabFin]
  rw [hcard, Nat.cast_one]

end MvPolynomial
