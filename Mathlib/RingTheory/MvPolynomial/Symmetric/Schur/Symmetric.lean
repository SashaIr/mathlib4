/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.Tableau.KostkaSymmetry
public import Mathlib.Data.Fintype.Sort
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.Kostka

/-!
# The Schur polynomials are symmetric

Following `theories/MPoly/Schur_mpoly.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we prove that the Schur polynomial
`s_μ` in `m` variables is a symmetric polynomial.

The coefficient of a monomial `x^d` in `s_μ` is the Kostka number counting the tableaux of
shape `μ` and content `d`, and the Kostka numbers are invariant under permuting the
letters (`Young.kostkaNum_permContent`), which is the combinatorial heart of the matter.

## Main results

* `MvPolynomial.coeff_schurPoly_eq_kostkaNum` : the coefficients of the Schur polynomial are the
  Kostka numbers.
* `MvPolynomial.schurPoly_isSymmetric` : the Schur polynomial is a symmetric polynomial.
-/

@[expose] public section

open Young

namespace MvPolynomial

open List MvPolynomial

variable {m : ℕ} {R : Type*} [CommSemiring R]

/-! ### Tableaux over `Fin m` and tableaux over `ℕ` with letters `< m` -/

lemma count_toWord {T : Type*} [DecidableEq T] (t : List (List T)) (a : T) :
    (toWord t).count a = t.flatten.count a := by
  rw [toWord, List.count_flatten, List.count_flatten, List.map_reverse, List.sum_reverse]

lemma exists_map_val {l : List ℕ} (h : ∀ x ∈ l, x < m) :
    ∃ l' : List (Fin m), l'.map Fin.val = l := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a l ih =>
    obtain ⟨l', hl'⟩ := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    exact ⟨(⟨a, h a (List.mem_cons_self ..)⟩ : Fin m) :: l', by simp [hl']⟩

lemma exists_mapTab_val {P : List (List ℕ)} (h : ∀ x ∈ P.flatten, x < m) :
    ∃ Q : List (List (Fin m)), mapTab (Fin.val : Fin m → ℕ) Q = P := by
  induction P with
  | nil => exact ⟨[], rfl⟩
  | cons p P ih =>
    have hcons : (p :: P).flatten = p ++ P.flatten := rfl
    have hp : ∀ x ∈ p, x < m := fun x hx => h x (by rw [hcons]; exact List.mem_append_left _ hx)
    have hP : ∀ x ∈ P.flatten, x < m :=
      fun x hx => h x (by rw [hcons]; exact List.mem_append_right _ hx)
    obtain ⟨Q, hQ⟩ := ih hP
    obtain ⟨p', hp'⟩ := exists_map_val hp
    exact ⟨p' :: Q, by rw [mapTab_cons, hp', hQ]⟩

/-- The content of a monomial, as a function `ℕ → ℕ`. -/
def finContent (m : ℕ) (d : Fin m →₀ ℕ) : ℕ → ℕ := fun i => if h : i < m then d ⟨i, h⟩ else 0

lemma sum_finContent (d : Fin m →₀ ℕ) :
    ∑ i ∈ Finset.range m, finContent m d i = ∑ j : Fin m, d j := by
  rw [Finset.sum_range]
  exact Finset.sum_congr rfl fun j _ => by simp [finContent, j.2]

lemma flatten_mapTab_val (Q : List (List (Fin m))) :
    (mapTab (Fin.val : Fin m → ℕ) Q).flatten = Q.flatten.map Fin.val := by
  rw [mapTab, List.map_flatten]

/-- The tableaux of shape `μ` over the alphabet `Fin m` with content `d` are exactly the
tableaux over `ℕ` of shape `μ` with letters `< m` and content `finContent m d`. -/
theorem card_ssyt_eq_kostkaNum (μ : List ℕ) (d : Fin m →₀ ℕ) :
    Nat.card {T : SSYT (Fin m) μ // (toWord T.1 : Multiset (Fin m)) = Finsupp.toMultiset d}
      = kostkaNum m μ (finContent m d) := by
  have hcount_iff : ∀ Q : List (List (Fin m)),
      ((toWord Q : Multiset (Fin m)) = Finsupp.toMultiset d) ↔
        (∀ i < m, (mapTab (Fin.val : Fin m → ℕ) Q).flatten.count i = finContent m d i) := by
    intro Q
    constructor
    · intro hQ i hi
      have hcount : ∀ j : Fin m, (toWord Q).count j = d j := by
        intro j
        have h : Multiset.count j (toWord Q : Multiset (Fin m))
            = Multiset.count j (Finsupp.toMultiset d) := by rw [hQ]
        simpa [Finsupp.count_toMultiset] using h
      rw [flatten_mapTab_val, count_map_val, dite_eq_left hi, ← count_toWord, hcount, finContent,
        dite_eq_left hi]
    · intro hQ
      refine Multiset.ext.2 fun j => ?_
      have hj := hQ j.1 j.2
      rw [flatten_mapTab_val, count_map_val, dite_eq_left j.2, finContent, dite_eq_left j.2] at hj
      simp only [Fin.eta] at hj
      rw [Finsupp.count_toMultiset]
      simpa [count_toWord] using hj
  have hmem : ∀ T : {T : SSYT (Fin m) μ // (toWord T.1 : Multiset (Fin m)) = Finsupp.toMultiset d},
      mapTab (Fin.val : Fin m → ℕ) T.1.1 ∈ tabSet m μ (finContent m d) := by
    intro T
    refine ⟨isTableau_mapTab_val T.1.2.1, by rw [shape_mapTab]; exact T.1.2.2, ?_,
      (hcount_iff _).1 T.2⟩
    intro x hx
    rw [flatten_mapTab_val] at hx
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    exact y.2
  rw [kostkaNum]
  refine Nat.card_congr (Equiv.ofBijective
    (fun T => (⟨mapTab (Fin.val : Fin m → ℕ) T.1.1, hmem T⟩ :
      tabSet m μ (finContent m d))) ⟨?_, ?_⟩)
  · rintro ⟨⟨P, hP⟩, hPd⟩ ⟨⟨Q, hQ⟩, hQd⟩ h
    have h' : mapTab (Fin.val : Fin m → ℕ) P = mapTab (Fin.val : Fin m → ℕ) Q :=
      congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext (mapTab_injective Fin.val_injective h'))
  · rintro ⟨P, hPtab, hPsh, hPlt, hPcount⟩
    obtain ⟨Q, rfl⟩ := exists_mapTab_val hPlt
    have hQtab : IsTableau Q := isTableau_of_isTableau_mapTab Fin.val_strictMono hPtab
    have hQsh : shape Q = μ := by rwa [shape_mapTab] at hPsh
    exact ⟨⟨⟨Q, hQtab, hQsh⟩, (hcount_iff Q).2 hPcount⟩, rfl⟩

/-- The coefficient of the monomial `x ^ d` in the Schur polynomial of shape `μ` is the
Kostka number counting the tableaux of shape `μ` and content `d`. -/
theorem coeff_schurPoly_eq_kostkaNum (μ : List ℕ) (d : Fin m →₀ ℕ) :
    coeff d (schurPoly (Fin m) R μ) = (kostkaNum m μ (finContent m d) : R) := by
  rw [coeff_schurPoly, card_ssyt_eq_kostkaNum]

/-! ### Symmetry -/

lemma finContent_mapDomain (e : Equiv.Perm (Fin m)) (d : Fin m →₀ ℕ) :
    finContent m (Finsupp.mapDomain e d) = permContent m (finContent m d) e.symm := by
  funext i
  by_cases h : i < m
  · have hmap : (Finsupp.mapDomain (e : Fin m → Fin m) d) ⟨i, h⟩ = d (e.symm ⟨i, h⟩) := by
      simp
    rw [finContent, dite_eq_left h, hmap, permContent, dite_eq_left h, finContent,
      dite_eq_left (e.symm ⟨i, h⟩).2, Fin.eta]
  · rw [finContent, dite_eq_right h, permContent, dite_eq_right h, finContent, dite_eq_right h]

/-- Permuting the variables of a monomial does not change its coefficient in the Schur
polynomial. -/
theorem coeff_schurPoly_mapDomain (μ : List ℕ) (d : Fin m →₀ ℕ) (e : Equiv.Perm (Fin m)) :
    coeff (Finsupp.mapDomain e d) (schurPoly (Fin m) R μ)
      = coeff d (schurPoly (Fin m) R μ) := by
  by_cases hμ : IsPart μ
  · rw [coeff_schurPoly_eq_kostkaNum, coeff_schurPoly_eq_kostkaNum, finContent_mapDomain]
    by_cases hsum : ∑ i ∈ Finset.range m, finContent m d i = μ.sum
    · rw [kostkaNum_permContent m e.symm μ (finContent m d) hμ hsum]
    · rw [kostkaNum_eq_zero_of_sum_ne _ _ _ hsum,
        kostkaNum_eq_zero_of_sum_ne _ _ _ (by rwa [sum_permContent])]
  · rw [schurPoly_eq_zero_of_not_isPart hμ, coeff_zero, coeff_zero]

/-- **The Schur polynomials are symmetric.** -/
theorem schurPoly_isSymmetric (μ : List ℕ) :
    (schurPoly (Fin m) R μ).IsSymmetric := by
  intro e
  refine MvPolynomial.ext _ _ fun d => ?_
  have hd : Finsupp.mapDomain (e : Fin m → Fin m) (Finsupp.mapDomain (e.symm : Fin m → Fin m) d)
      = d := by
    rw [← Finsupp.mapDomain_comp]
    simp
  rw [← hd, coeff_rename_mapDomain _ e.injective, hd, coeff_schurPoly_mapDomain μ d e.symm]

/-! ### An arbitrary finite alphabet -/

section Alphabet

variable {σ τ ρ : Type*} [LinearOrder σ] [LinearOrder τ] [LinearOrder ρ]

omit [LinearOrder σ] [LinearOrder τ] [LinearOrder ρ] in
lemma mapTab_mapTab (g : τ → ρ) (f : σ → τ) (P : List (List σ)) :
    mapTab g (mapTab f P) = mapTab (g ∘ f) P := by
  simp [mapTab, List.map_map, Function.comp_def]

omit [LinearOrder σ] in
@[simp] lemma mapTab_id (P : List (List σ)) : mapTab id P = P := by
  simp [mapTab]

/-- An order isomorphism of alphabets induces a bijection of the tableaux of a given
shape. -/
def ssytEquivOfOrderIso (f : σ ≃o τ) (μ : List ℕ) : SSYT σ μ ≃ SSYT τ μ where
  toFun T := ⟨mapTab f T.1, isTableau_mapTab f.strictMono T.2.1, by
    rw [shape_mapTab]; exact T.2.2⟩
  invFun T := ⟨mapTab f.symm T.1, isTableau_mapTab f.symm.strictMono T.2.1, by
    rw [shape_mapTab]; exact T.2.2⟩
  left_inv T := Subtype.ext (by
    change mapTab (f.symm : τ → σ) (mapTab (f : σ → τ) T.1) = T.1
    rw [mapTab_mapTab, show (f.symm : τ → σ) ∘ (f : σ → τ) = id from funext fun x => by simp,
      mapTab_id])
  right_inv T := Subtype.ext (by
    change mapTab (f : σ → τ) (mapTab (f.symm : τ → σ) T.1) = T.1
    rw [mapTab_mapTab, show (f : σ → τ) ∘ (f.symm : τ → σ) = id from funext fun x => by simp,
      mapTab_id])

/-- The Schur polynomials over two order-isomorphic alphabets correspond to each other
under renaming of the variables. -/
theorem rename_schurPoly [Fintype σ] [Fintype τ] (f : σ ≃o τ) (μ : List ℕ) :
    rename (f : σ → τ) (schurPoly σ R μ) = schurPoly τ R μ := by
  rw [schurPoly, map_sum]
  refine Fintype.sum_equiv (ssytEquivOfOrderIso f μ) _ _ fun T => ?_
  change rename (f : σ → τ) (((toWord T.1).map X).prod)
    = ((toWord (mapTab (f : σ → τ) T.1)).map X).prod
  rw [toWord_mapTab, map_list_prod, List.map_map, List.map_map]
  simp [Function.comp_def]

/-- **The Schur polynomials are symmetric**, over an arbitrary finite alphabet of
variables. -/
theorem schurPoly_isSymmetric_of_fintype [Fintype σ] (μ : List ℕ) :
    (schurPoly σ R μ).IsSymmetric := by
  have e : Fin (Fintype.card σ) ≃o σ := monoEquivOfFin σ rfl
  have h : rename (e.toEquiv : Fin (Fintype.card σ) → σ) (schurPoly (Fin (Fintype.card σ)) R μ)
      = schurPoly σ R μ := rename_schurPoly e μ
  rw [← h]
  exact (schurPoly_isSymmetric μ).rename e.toEquiv

end Alphabet

end MvPolynomial
