/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.Tableau.Basic
public import Mathlib.Data.Fintype.Vector
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
# Schur polynomials

Following `theories/MPoly/Schur_mpoly.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), the *Schur polynomial* of a shape
`sh` in the (finitely many) variables `σ` is the sum, over all Young tableaux of shape
`sh` with entries in `σ`, of the monomial recording the content of the tableau.

## Main definitions

* `MvPolynomial.SSYT σ sh` : the type of Young tableaux of shape `sh` with entries in `σ`.
* `MvPolynomial.schurPoly σ R sh` : the Schur polynomial of shape `sh`.

## Main results

* `MvPolynomial.coeff_schurPoly` : the coefficient of a monomial in the Schur polynomial is the
  number of tableaux of shape `sh` with that content (a Kostka number).
* `MvPolynomial.schurPoly_row` : the Schur polynomial of a one-row shape is the complete
  homogeneous symmetric polynomial.
* `MvPolynomial.schurPoly_column` : the Schur polynomial of a one-column shape is the elementary
  symmetric polynomial.
-/

@[expose] public section

namespace MvPolynomial

open List MvPolynomial

variable {σ : Type*} [LinearOrder σ]

/-! ### Tableaux of a given shape form a finite type -/

/-- The type of Young tableaux of shape `sh` with entries in `σ`. -/
def SSYT (σ : Type*) [LinearOrder σ] (sh : List ℕ) : Type _ :=
  {P : List (List σ) // IsTableau P ∧ shape P = sh}

instance (sh : List ℕ) : DecidableEq (SSYT σ sh) := fun _ _ =>
  decidable_of_iff _ Subtype.ext_iff.symm

instance finite_SSYT [Finite σ] (sh : List ℕ) : Finite (SSYT σ sh) := by
  have hfin : Finite {w : List σ // w.length = sh.sum} :=
    inferInstanceAs (Finite (List.Vector σ sh.sum))
  refine Finite.of_injective
    (fun T : SSYT σ sh => (⟨T.1.flatten, ?_⟩ : {w : List σ // w.length = sh.sum})) ?_
  · rw [List.length_flatten]
    exact congrArg List.sum T.2.2
  · rintro ⟨P, hP, hPs⟩ ⟨Q, hQ, hQs⟩ h
    have hf : P.flatten = Q.flatten := congrArg Subtype.val h
    exact Subtype.ext (eq_of_shape_eq_of_flatten_eq (by rw [hPs, hQs]) hf)

noncomputable instance fintypeSSYT [Finite σ] (sh : List ℕ) : Fintype (SSYT σ sh) :=
  Fintype.ofFinite _

/-! ### The Schur polynomial -/

/-- The Schur polynomial of shape `sh`: the sum over all tableaux of shape `sh` with
entries in `σ` of the monomial recording the content of the tableau. -/
noncomputable def schurPoly (σ : Type*) [Fintype σ] [LinearOrder σ] (R : Type*)
    [CommSemiring R] (sh : List ℕ) : MvPolynomial σ R :=
  ∑ T : SSYT σ sh, ((toWord T.1).map X).prod

variable {R : Type*} [CommSemiring R]

/-- The product of the variables indexed by a word is the monomial recording its content. -/
lemma prod_map_X (l : List σ) :
    ((l.map (X : σ → MvPolynomial σ R)).prod) =
      monomial (Multiset.toFinsupp (l : Multiset σ)) 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, ih]
    rw [show (X a : MvPolynomial σ R) = monomial (Finsupp.single a 1) 1 from rfl,
      monomial_mul_monomial,
      one_mul, ← Multiset.cons_coe, ← Multiset.singleton_add, Multiset.toFinsupp_add,
      Multiset.toFinsupp_singleton]

/-- The coefficient of the monomial `x ^ d` in the Schur polynomial of shape `sh` is the
number of tableaux of shape `sh` and content `d`, i.e. a Kostka number. -/
theorem coeff_schurPoly [Fintype σ] (sh : List ℕ) (d : σ →₀ ℕ) :
    coeff d (schurPoly σ R sh) =
      (Nat.card {T : SSYT σ sh // (toWord T.1 : Multiset σ) = Finsupp.toMultiset d} : R) := by
  rw [schurPoly, coeff_sum]
  simp only [prod_map_X, coeff_monomial]
  rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  refine congrArg Finset.card (Finset.filter_congr fun T _ => ?_)
  simp [Multiset.toFinsupp_eq_iff]

/-- The empty shape has a unique tableau, the empty one. -/
instance uniqueSSYTNil : Unique (SSYT σ ([] : List ℕ)) where
  default := ⟨[], trivial, rfl⟩
  uniq := by
    rintro ⟨P, hP, hPs⟩
    refine Subtype.ext ?_
    cases P with
    | nil => rfl
    | cons p P => simp at hPs

@[simp] lemma schurPoly_nil [Fintype σ] : schurPoly σ R [] = 1 := by
  rw [schurPoly, Fintype.sum_unique]
  rfl

/-- There is no tableau whose shape is not a partition, so the Schur polynomial of such a
shape vanishes. -/
theorem schurPoly_eq_zero_of_not_isPart [Fintype σ] {sh : List ℕ} (hsh : ¬ IsPart sh) :
    schurPoly σ R sh = 0 := by
  have : IsEmpty (SSYT σ sh) := by
    constructor
    rintro ⟨P, hP, rfl⟩
    exact hsh (isPart_shape hP)
  rw [schurPoly, Finset.univ_eq_empty, Finset.sum_empty]

/-- The Schur polynomial of shape `sh` is homogeneous of degree the number of boxes of
`sh`. -/
theorem isHomogeneous_schurPoly [Fintype σ] (sh : List ℕ) :
    (schurPoly σ R sh).IsHomogeneous sh.sum := by
  rw [schurPoly]
  refine IsHomogeneous.sum _ _ _ fun T _ => ?_
  rw [prod_map_X]
  refine isHomogeneous_monomial 1 ?_
  have hlen := length_toWord T.1
  rw [sizeTab, T.2.2] at hlen
  have hdeg : (Multiset.toFinsupp (toWord T.1 : Multiset σ)).degree
      = Multiset.card (toWord T.1 : Multiset σ) := by
    have h := Finsupp.card_toMultiset (Multiset.toFinsupp (toWord T.1 : Multiset σ))
    rw [Multiset.toFinsupp_toMultiset] at h
    rw [h, Finsupp.degree]
    rfl
  rw [hdeg]
  simpa using hlen

/-- Evaluating all the variables at `1` in the Schur polynomial of shape `sh` counts the
tableaux of shape `sh`. -/
theorem eval_one_schurPoly [Fintype σ] (sh : List ℕ) :
    eval (fun _ => (1 : R)) (schurPoly σ R sh) = (Fintype.card (SSYT σ sh) : R) := by
  have h1 : ∀ T : SSYT σ sh, eval (fun _ => (1 : R)) (((toWord T.1).map X).prod) = 1 := by
    intro T
    rw [prod_map_X, eval_monomial]
    simp
  rw [schurPoly, map_sum]
  simp [h1, Finset.card_univ]

/-! ### One-row shapes: the complete homogeneous symmetric polynomials -/

lemma isTableau_singleton {r : List σ} (hne : r ≠ []) (hr : IsRow r) : IsTableau [r] :=
  ⟨hne, hr, by simp, trivial⟩

lemma isRow_sort (s : Multiset σ) : IsRow (s.sort (· ≤ ·)) :=
  List.isChain_iff_pairwise.2 (Multiset.pairwise_sort s _)

omit [LinearOrder σ] in
lemma exists_row_of_shape_singleton {P : List (List σ)} {n : ℕ} (h : shape P = [n]) :
    ∃ r : List σ, P = [r] ∧ r.length = n := by
  cases P with
  | nil => simp [shape] at h
  | cons r P =>
    cases P with
    | nil => exact ⟨r, rfl, by simpa using h⟩
    | cons r' P => simp at h

/-- The tableau with the single row obtained by sorting a multiset. -/
def rowTabOfSym {n : ℕ} (hn : 0 < n) (s : Sym σ n) : SSYT σ [n] :=
  ⟨[s.1.sort (· ≤ ·)],
    isTableau_singleton (by
      intro hc
      have : (s.1.sort (· ≤ ·)).length = n := by rw [Multiset.length_sort, s.2]
      rw [hc] at this
      simp at this
      omega) (isRow_sort s.1),
    by simp [Multiset.length_sort]⟩

/-- The multiset of the entries of a tableau with a single row. -/
def symOfRowTab {n : ℕ} (T : SSYT σ [n]) : Sym σ n :=
  ⟨(toWord T.1 : Multiset σ), by
    have := length_toWord T.1
    rw [sizeTab, T.2.2] at this
    simp [this]⟩

/-- The Schur polynomial of the one-row shape `[n]` is the complete homogeneous symmetric
polynomial `hsymm n`. -/
theorem schurPoly_row [Fintype σ] {n : ℕ} (hn : 0 < n) : schurPoly σ R [n] = hsymm σ R n := by
  classical
  rw [schurPoly, hsymm]
  refine Finset.sum_nbij' (fun T => symOfRowTab T) (fun s => rowTabOfSym hn s)
    (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro T _
    obtain ⟨r, hr, hrn⟩ := exists_row_of_shape_singleton T.2.2
    have hrow : IsRow r := by
      have := T.2.1
      rw [hr] at this
      exact this.2.1
    refine Subtype.ext ?_
    change [((toWord T.1 : Multiset σ)).sort (· ≤ ·)] = T.1
    rw [hr]
    have hw : toWord ([r] : List (List σ)) = r := by simp [toWord]
    rw [hw]
    congr 1
    refine List.Perm.eq_of_pairwise (fun a b _ _ hab hba => le_antisymm hab hba)
      (Multiset.pairwise_sort _ _) (List.isChain_iff_pairwise.1 hrow) ?_
    exact Quotient.exact (Multiset.sort_eq (r : Multiset σ) (· ≤ ·))
  · intro s _
    refine Subtype.ext ?_
    change ((toWord [s.1.sort (· ≤ ·)] : List σ) : Multiset σ) = s.1
    rw [show toWord [s.1.sort (· ≤ ·)] = s.1.sort (· ≤ ·) by simp [toWord]]
    exact Multiset.sort_eq _ _
  · intro T _
    change ((toWord T.1).map X).prod = ((symOfRowTab T).1.map X).prod
    simp [symOfRowTab]

/-! ### One-column shapes: the elementary symmetric polynomials -/

/-- The one-column tableau with the given entries. -/
def colTab (l : List σ) : List (List σ) := l.map (fun a => [a])

omit [LinearOrder σ] in
@[simp] lemma shape_colTab (l : List σ) : shape (colTab l) = List.replicate l.length 1 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have hc : colTab (a :: l) = [a] :: colTab l := rfl
    rw [hc, shape_cons, ih]
    simp [List.replicate_succ]

omit [LinearOrder σ] in
@[simp] lemma toWord_colTab (l : List σ) : toWord (colTab l) = l.reverse := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have : colTab (a :: l) = [a] :: colTab l := rfl
    rw [this, toWord_cons, ih]
    simp

lemma isTableau_colTab_iff (l : List σ) : IsTableau (colTab l) ↔ List.IsChain (· < ·) l := by
  induction l with
  | nil => simp [colTab]
  | cons a l ih =>
    have hc : colTab (a :: l) = [a] :: colTab l := rfl
    rw [hc, isTableau_cons, ih]
    cases l with
    | nil => simp [colTab, IsRow]
    | cons b l =>
      have hhead : (colTab (b :: l)).headD [] = [b] := rfl
      rw [hhead]
      simp [IsRow, List.isChain_cons_cons, and_comm]

omit [LinearOrder σ] in
lemma exists_list_of_shape_replicate {P : List (List σ)} {k : ℕ}
    (h : shape P = List.replicate k 1) : ∃ l : List σ, l.length = k ∧ P = colTab l := by
  induction k generalizing P with
  | zero =>
    cases P with
    | nil => exact ⟨[], rfl, rfl⟩
    | cons p P => simp at h
  | succ k ih =>
    cases P with
    | nil => simp at h
    | cons p P =>
      rw [List.replicate_succ, shape_cons, List.cons.injEq] at h
      obtain ⟨hp, hP⟩ := h
      obtain ⟨a, rfl⟩ : ∃ a, p = [a] := by
        match p, hp with
        | [a], _ => exact ⟨a, rfl⟩
      obtain ⟨l, hl, rfl⟩ := ih hP
      exact ⟨a :: l, by simp [hl], rfl⟩

lemma pairwise_lt_sort (t : Finset σ) : List.Pairwise (· < ·) (t.sort (· ≤ ·)) :=
  (Finset.pairwise_sort t _).imp₂ (fun _ _ => lt_of_le_of_ne) (t.sort_nodup _)

lemma isTableau_colTab_sort (t : Finset σ) : IsTableau (colTab (t.sort (· ≤ ·))) :=
  (isTableau_colTab_iff _).2 (List.isChain_iff_pairwise.2 (pairwise_lt_sort t))

/-- A one-column tableau is the sorted list of the letters it contains. -/
lemma eq_colTab_sort {k : ℕ} (T : SSYT σ (List.replicate k 1)) :
    T.1 = colTab ((toWord T.1).toFinset.sort (· ≤ ·)) := by
  classical
  obtain ⟨l, hl, hT⟩ := exists_list_of_shape_replicate T.2.2
  have hchain : List.IsChain (· < ·) l := by
    rw [← isTableau_colTab_iff, ← hT]; exact T.2.1
  have hpair : List.Pairwise (· < ·) l := List.isChain_iff_pairwise.1 hchain
  have hnd : l.Nodup := hpair.imp (fun h => ne_of_lt h)
  have hsort : l.toFinset.sort (· ≤ ·) = l :=
    (List.toFinset_sort (· ≤ ·) hnd).2 (hpair.imp (fun h => le_of_lt h))
  rw [hT, toWord_colTab, List.toFinset_reverse, hsort]

/-- The Schur polynomial of the one-column shape `1 ^ k` is the elementary symmetric
polynomial `esymm k`. -/
theorem schurPoly_column [Fintype σ] (k : ℕ) :
    schurPoly σ R (List.replicate k 1) = esymm σ R k := by
  classical
  have hnodup : ∀ T : SSYT σ (List.replicate k 1), (toWord T.1).Nodup := by
    intro T
    obtain ⟨l, hl, hT⟩ := exists_list_of_shape_replicate T.2.2
    have hchain : List.IsChain (· < ·) l := by
      rw [← isTableau_colTab_iff, ← hT]; exact T.2.1
    have hnd : l.Nodup := (List.isChain_iff_pairwise.1 hchain).imp (fun h => ne_of_lt h)
    rw [hT, toWord_colTab]
    exact List.nodup_reverse.2 hnd
  have hcard : ∀ T : SSYT σ (List.replicate k 1), (toWord T.1).toFinset.card = k := by
    intro T
    rw [List.toFinset_card_of_nodup (hnodup T)]
    have hlen := length_toWord T.1
    rw [sizeTab, T.2.2] at hlen
    simpa using hlen
  rw [schurPoly, esymm]
  refine Finset.sum_bij (fun (T : SSYT σ (List.replicate k 1)) _ => (toWord T.1).toFinset)
    (fun T _ => Finset.mem_powersetCard_univ.2 (hcard T)) ?_ ?_ ?_
  · intro T1 _ T2 _ h
    refine Subtype.ext ?_
    have h' : (toWord T1.1).toFinset = (toWord T2.1).toFinset := h
    rw [eq_colTab_sort T1, eq_colTab_sort T2, h']
  · intro t ht
    have hct : t.card = k := Finset.mem_powersetCard_univ.1 ht
    refine ⟨⟨colTab (t.sort (· ≤ ·)), isTableau_colTab_sort t, ?_⟩, Finset.mem_univ _, ?_⟩
    · rw [shape_colTab, Finset.length_sort, hct]
    · change (toWord (colTab (t.sort (· ≤ ·)))).toFinset = t
      rw [toWord_colTab, List.toFinset_reverse, Finset.sort_toFinset]
  · intro T _
    change ((toWord T.1).map X).prod = ∏ i ∈ (toWord T.1).toFinset, X i
    rw [List.prod_toFinset _ (hnodup T)]

end MvPolynomial
