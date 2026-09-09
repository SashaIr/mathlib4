/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Young.Tableau.Kostka
import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.Basic

/-!
# Schur polynomials and Kostka numbers

The coefficients of the Schur polynomial `s_sh` are Kostka numbers, so the results of
`Mathlib/Combinatorics/Young/Tableau/Kostka.lean` on Kostka numbers translate into statements
about `s_sh`: the monomial `x ^ d` occurs only if the shape `sh` dominates the content `d`, and the
monomial of content `sh` itself occurs exactly once.  In other words

`s_λ = m_λ + (terms of content strictly dominated by λ)`.

## Main definitions

* `MvPolynomial.mapTab f P` : the image of a tableau under a map of the alphabet.

## Main results

* `List.isTableau_mapTab` : a strictly monotone map of alphabets sends tableaux to
  tableaux.
* `MvPolynomial.coeff_schurPoly_eq_zero_of_not_partdom` : the coefficient of `x ^ d` in `s_sh`
  vanishes unless `sh` dominates the content `d`.
* `MvPolynomial.coeff_schurPoly_self` : the coefficient of the monomial of content `sh` in
  `s_sh` is `1`.
-/

/-! ### Tableaux under a map of the alphabet -/

namespace List

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

end List

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

/-- The coefficient of `x ^ d` in the Schur polynomial of shape `sh` vanishes unless `sh`
dominates the content `d`. -/
theorem coeff_schurPoly_eq_zero_of_not_partdom (sh : List ℕ) (d : Fin m →₀ ℕ)
    (h : ¬ Partdom (List.ofFn fun i : Fin m => d i) sh) :
    coeff d (schurPoly (Fin m) R sh) = 0 := by
  classical
  rw [coeff_schurPoly]
  have hempty : IsEmpty
      {T : SSYT (Fin m) sh // (toWord T.1 : Multiset (Fin m)) = Finsupp.toMultiset d} := by
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
theorem schurPoly_eq_zero_of_lt_length {sh : List ℕ} (hlen : m < sh.length) :
    schurPoly (Fin m) R sh = 0 := by
  have : IsEmpty (SSYT (Fin m) sh) := by
    constructor
    rintro ⟨P, hP, hsh⟩
    have := length_le_of_isTableau hP
    have hlength : P.length = sh.length := by
      simpa [shape] using congrArg List.length hsh
    omega
  rw [schurPoly, Finset.univ_eq_empty, Finset.sum_empty]

/-! ### The coefficient of the monomial of content the shape -/

/-- The exponent vector recording the content `sh` over the alphabet `Fin m`. -/
noncomputable def shapeContent (m : ℕ) (sh : List ℕ) : Fin m →₀ ℕ :=
  Finsupp.onFinset Finset.univ (fun i : Fin m => sh.getD i 0) (fun _ _ => Finset.mem_univ _)

@[simp] lemma shapeContent_apply (sh : List ℕ) (i : Fin m) :
    shapeContent m sh i = sh.getD i 0 := rfl

/-- The superstandard tableau of shape `sh` over the alphabet `Fin m`: its `i`-th row
consists of `sh i` copies of the letter `i`. -/
def superTabFin (m : ℕ) (sh : List ℕ) (hlen : sh.length ≤ m) : List (List (Fin m)) :=
  List.ofFn fun j : Fin sh.length =>
    List.replicate (sh.getD j 0) (⟨j, lt_of_lt_of_le j.2 hlen⟩ : Fin m)

lemma mapTab_val_superTabFin (sh : List ℕ) (hlen : sh.length ≤ m) :
    mapTab (Fin.val : Fin m → ℕ) (superTabFin m sh hlen) = superTab sh := by
  have hlength : (superTab sh).length = sh.length := by
    simpa [shape] using congrArg List.length (shape_superTab sh)
  refine List.ext_getElem (by simp [superTabFin, mapTab, hlength]) fun j h1 h2 => ?_
  have hj : j < sh.length := by omega
  have hlhs : (mapTab (Fin.val : Fin m → ℕ) (superTabFin m sh hlen))[j]'h1
      = List.replicate (sh.getD j 0) j := by
    simp [mapTab, superTabFin, List.map_replicate, List.getElem?_eq_getElem hj]
  rw [hlhs, ← List.getD_eq_getElem _ _ h2, getD_superTab]

lemma isTableau_superTabFin {sh : List ℕ} (hsh : IsPart sh) (hlen : sh.length ≤ m) :
    IsTableau (superTabFin m sh hlen) :=
  isTableau_of_isTableau_mapTab Fin.val_strictMono
    (by rw [mapTab_val_superTabFin]; exact isTableau_superTab hsh)

lemma shape_superTabFin (sh : List ℕ) (hlen : sh.length ≤ m) :
    shape (superTabFin m sh hlen) = sh := by
  rw [← shape_mapTab (Fin.val : Fin m → ℕ), mapTab_val_superTabFin, shape_superTab]

lemma count_toWord_superTabFin (sh : List ℕ) (hlen : sh.length ≤ m) (j : Fin m) :
    (toWord (superTabFin m sh hlen)).count j = sh.getD j 0 := by
  have h := count_toWord_superTab sh (j : ℕ)
  rw [← mapTab_val_superTabFin sh hlen, toWord_mapTab, count_map_val, dite_eq_left j.2] at h
  simpa using h

/-- The coefficient of the monomial of content `sh` in the Schur polynomial of shape `sh`
is `1`: `s_sh = m_sh + (terms of content strictly dominated by sh)`. -/
theorem coeff_schurPoly_self {sh : List ℕ} (hsh : IsPart sh) (hlen : sh.length ≤ m) :
    coeff (shapeContent m sh) (schurPoly (Fin m) R sh) = 1 := by
  classical
  rw [coeff_schurPoly]
  have hgetD : ∀ i : ℕ, (List.ofFn fun j : Fin m => shapeContent m sh j).getD i 0
      = sh.getD i 0 := by
    intro i
    by_cases hi : i < m
    · rw [List.getD_eq_getElem _ _ (by simpa using hi)]
      simp
    · rw [List.getD_eq_default _ _ (by simpa using hi),
        List.getD_eq_default _ _ (by omega)]
  have hcontent : ∀ P : List (List (Fin m)),
      ((toWord P : Multiset (Fin m)) = Finsupp.toMultiset (shapeContent m sh))
        ↔ ∀ j : Fin m, (toWord P).count j = sh.getD j 0 := by
    intro P
    rw [Multiset.ext]
    constructor
    · intro h j
      simpa [Finsupp.count_toMultiset] using h j
    · intro h j
      simpa [Finsupp.count_toMultiset] using h j
  have hcard : Nat.card {T : SSYT (Fin m) sh //
      (toWord T.1 : Multiset (Fin m)) = Finsupp.toMultiset (shapeContent m sh)} = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨⟨superTabFin m sh hlen, isTableau_superTabFin hsh hlen, shape_superTabFin sh hlen⟩,
      (hcontent _).2 (count_toWord_superTabFin sh hlen)⟩, ?_⟩
    rintro ⟨T, hT⟩
    refine Subtype.ext (Subtype.ext ?_)
    have ht : IsTableau (mapTab (Fin.val : Fin m → ℕ) T.1) := isTableau_mapTab_val T.2.1
    have hshape : shape (mapTab (Fin.val : Fin m → ℕ) T.1) = sh := by
      rw [shape_mapTab, T.2.2]
    have hev : evalseq (toWord (mapTab (Fin.val : Fin m → ℕ) T.1)) = sh := by
      refine ext_getD_of_getLastD_ne_zero (getLastD_evalseq_ne_zero _) hsh.getLastD_ne_zero ?_
      intro i
      rw [getD_evalseq, toWord_mapTab, count_toWord_map_val hT i, hgetD i]
    have hsuper := eq_superTab_of_evalseq_eq ht (by rw [hev, hshape])
    rw [hshape] at hsuper
    refine mapTab_injective (f := (Fin.val : Fin m → ℕ)) Fin.val_injective ?_
    rw [hsuper, mapTab_val_superTabFin]
  rw [hcard, Nat.cast_one]

end MvPolynomial
