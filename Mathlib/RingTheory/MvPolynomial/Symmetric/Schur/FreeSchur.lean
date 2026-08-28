/-
Copyright (c) 2026 Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/
import Mathlib.Data.List.Permutation
import Mathlib.Combinatorics.Young.LittlewoodRichardson.LangQ
import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.Basic
import Mathlib.RingTheory.MvPolynomial.WordLanguage

/-!
# Free Schur functions and the Littlewood–Richardson rule for tableaux

A Lean 4 port of `theories/LRrule/freeSchur.v` from
[Coq-Combi](https://github.com/math-comp/Coq-Combi).

The *free Schur function* attached to a standard tableau `Q` is the (noncommutative) sum of
the words whose recording tableau is `Q`, that is, of the language `List.langQ σ Q`.  Its
commutative image is the Schur polynomial of the shape of `Q`: the Robinson–Schensted
correspondence matches the words of that language with the tableaux of that shape.

Combined with the free Littlewood–Richardson rule `List.LRrule_langQ`, this gives the
Littlewood–Richardson rule in its tableau form: the product of two Schur polynomials is the
sum of the Schur polynomials of the shapes of the standard tableaux completing the two given
ones into a Littlewood–Richardson triple.

## Main results

* `MvPolynomial.schurPoly_eq_sum_langQ` : the commutative image of the free Schur function of
  `Q` is the Schur polynomial of the shape of `Q` (Coq `Schur_freeSchurE`).
* `MvPolynomial.polyLang_langQ` : the same statement in terms of the generating polynomial
  of a language.
* `MvPolynomial.catLang_langQ` : **the free Littlewood–Richardson rule** as an identity
  between languages (Coq `free_LR_rule`).
* `MvPolynomial.schurPoly_mul_eq_sum_LRtriple` : **the Littlewood–Richardson rule for
  tableaux** (Coq `LR_rule_tab`).
-/

namespace MvPolynomial

open List MvPolynomial

variable {σ : Type*} [LinearOrder σ] {R : Type*} [CommSemiring R]

/-! ### The Robinson–Schensted bijection between a language and the tableaux of a shape -/

/-- The insertion tableau is a bijection between the words whose recording tableau is the
standard tableau `Q` and the tableaux of the shape of `Q` (Coq
`tabword_of_tuple_freeSchur`). -/
theorem RS_bijOn_langQ {Q : List (List ℕ)} (hQ : IsStdTab Q) :
    Set.BijOn RS (langQ σ Q) {P : List (List σ) | IsTableau P ∧ shape P = shape Q} := by
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    exact ⟨isTableau_RS w, by rw [← shape_RSQ w, mem_langQ.1 hw]⟩
  · intro u hu v hv h
    exact RS_RSQ_injective h (by rw [mem_langQ.1 hu, mem_langQ.1 hv])
  · rintro P ⟨hP, hsh⟩
    obtain ⟨w, h1, h2⟩ := exists_word_RS_RSQ hP hQ hsh.symm
    exact ⟨w, h2, h1⟩

/-- The words whose recording tableau is a given tableau have a fixed length, hence form a
finite set. -/
instance finite_langQ [Finite σ] (Q : List (List ℕ)) : Finite (langQ σ Q) := by
  have hfin : Finite {w : List σ // w.length = sizeTab Q} :=
    inferInstanceAs (Finite (List.Vector σ (sizeTab Q)))
  refine Finite.of_injective
    (fun w : langQ σ Q => (⟨w.1, length_eq_sizeTab_of_mem_langQ w.2⟩ :
      {w : List σ // w.length = sizeTab Q})) ?_
  rintro ⟨u, hu⟩ ⟨v, hv⟩ h
  have : u = v := congrArg Subtype.val h
  exact Subtype.ext this

noncomputable instance fintype_langQ [Finite σ] (Q : List (List ℕ)) : Fintype (langQ σ Q) :=
  Fintype.ofFinite _

/-- The Robinson–Schensted correspondence as an equivalence between the language of a
standard tableau `Q` and the tableaux of the shape of `Q`. -/
noncomputable def langQEquivSSYT {Q : List (List ℕ)} (hQ : IsStdTab Q) :
    langQ σ Q ≃ SSYT σ (shape Q) :=
  (RS_bijOn_langQ hQ).equiv

/-! ### The commutative image of a free Schur function -/

/-- **The commutative image of the free Schur function of a standard tableau `Q` is the Schur
polynomial of the shape of `Q`** (Coq `Schur_freeSchurE`). -/
theorem schurPoly_eq_sum_langQ [Fintype σ] {Q : List (List ℕ)} (hQ : IsStdTab Q) :
    schurPoly σ R (shape Q) = ∑ w : langQ σ Q, ((w.1.map (X : σ → MvPolynomial σ R)).prod) := by
  rw [schurPoly]
  refine (Fintype.sum_equiv (langQEquivSSYT (σ := σ) hQ) _ _ ?_).symm
  intro w
  exact (List.Perm.prod_eq ((perm_toWord_RS w.1).map (X : σ → MvPolynomial σ R))).symm

/-- The language of a standard tableau is homogeneous: all its words have as many letters as
the tableau has boxes. -/
lemma isHomLang_langQ (Q : List (List ℕ)) : IsHomLang (sizeTab Q) (langQ σ Q) :=
  fun _ hw => length_eq_sizeTab_of_mem_langQ hw

/-- **The generating polynomial of the language of a standard tableau `Q` is the Schur
polynomial of the shape of `Q`** (Coq `Schur_freeSchurE`). -/
theorem polyLang_langQ [Fintype σ] {Q : List (List ℕ)} (hQ : IsStdTab Q) :
    polyLang R (langQ σ Q) = schurPoly σ R (shape Q) :=
  (schurPoly_eq_sum_langQ hQ).symm

/-! ### The Littlewood–Richardson rule for tableaux -/

/-- Standard tableaux with a given number of boxes form a finite type. -/
instance finite_stdTabOfSize (n : ℕ) :
    Finite {Q : List (List ℕ) // IsStdTab Q ∧ sizeTab Q = n} := by
  refine Finite.of_injective
    (fun Q : {Q : List (List ℕ) // IsStdTab Q ∧ sizeTab Q = n} =>
      (⟨toWord Q.1, ?_⟩ : {w : List ℕ // w ∈ (List.range n).permutations})) ?_
  · refine List.mem_permutations.2 ?_
    have h := Q.2.1.2
    rw [IsStd, length_toWord, Q.2.2] at h
    exact h
  · rintro ⟨P, hP⟩ ⟨Q, hQ⟩ h
    have hw : toWord P = toWord Q := congrArg Subtype.val h
    have : P = Q := by rw [← RS_toWord hP.1.1, hw, RS_toWord hQ.1.1]
    exact Subtype.ext this

variable {Q₁ Q₂ : List (List ℕ)}

/-- The standard tableaux completing `Q₁` and `Q₂` into a Littlewood–Richardson triple (Coq
`LRsupport`). -/
def LRsupport (Q₁ Q₂ : List (List ℕ)) : Type :=
  {Q : List (List ℕ) // (IsStdTab Q ∧ sizeTab Q = sizeTab Q₁ + sizeTab Q₂) ∧ LRtriple Q₁ Q₂ Q}

instance : Finite (LRsupport Q₁ Q₂) := by
  refine Finite.of_injective (fun Q : LRsupport Q₁ Q₂ => (⟨Q.1, Q.2.1⟩ :
      {Q : List (List ℕ) // IsStdTab Q ∧ sizeTab Q = sizeTab Q₁ + sizeTab Q₂})) ?_
  rintro ⟨P, hP⟩ ⟨Q, hQ⟩ h
  have : P = Q := congrArg Subtype.val h
  exact Subtype.ext this

noncomputable instance : Fintype (LRsupport Q₁ Q₂) := Fintype.ofFinite _

/-- Splitting a word of the language of a member of the Littlewood–Richardson support at the
size of `Q₁` gives a word of the language of `Q₁` and a word of the language of `Q₂`. -/
lemma mem_langQ_take_drop (hQ₁ : IsStdTab Q₁) {Q : List (List ℕ)} (hLR : LRtriple Q₁ Q₂ Q)
    {w : List σ} (hw : w ∈ langQ σ Q) :
    w.take (sizeTab Q₁) ∈ langQ σ Q₁ ∧ w.drop (sizeTab Q₁) ∈ langQ σ Q₂ := by
  obtain ⟨u, v, rfl, hu, hv⟩ := (LRrule_langQ hQ₁ w).2 ⟨Q, hLR, hw⟩
  have hlen : u.length = sizeTab Q₁ := length_eq_sizeTab_of_mem_langQ hu
  rw [← hlen, List.take_left, List.drop_left]
  exact ⟨hu, hv⟩

/-- The pairs of words of the languages of `Q₁` and `Q₂` are in bijection, via concatenation,
with the words of the languages of the standard tableaux of the Littlewood–Richardson support
of `Q₁` and `Q₂` (Coq `free_LR_rule`). -/
def langQProdEquivSigma (hQ₁ : IsStdTab Q₁) (hQ₂ : IsStdTab Q₂) :
    langQ σ Q₁ × langQ σ Q₂ ≃ Σ Q : LRsupport Q₁ Q₂, langQ σ Q.1 where
  toFun p :=
    ⟨⟨RSQ (p.1.1 ++ p.2.1),
      isStdTab_of_LRtriple hQ₁ hQ₂ (LRtriple_RSQ_append p.1.2 p.2.2),
      LRtriple_RSQ_append p.1.2 p.2.2⟩, ⟨p.1.1 ++ p.2.1, rfl⟩⟩
  invFun q :=
    (⟨q.2.1.take (sizeTab Q₁), (mem_langQ_take_drop hQ₁ q.1.2.2 q.2.2).1⟩,
     ⟨q.2.1.drop (sizeTab Q₁), (mem_langQ_take_drop hQ₁ q.1.2.2 q.2.2).2⟩)
  left_inv p := by
    have hlen : p.1.1.length = sizeTab Q₁ := length_eq_sizeTab_of_mem_langQ p.1.2
    ext1 <;> simp [← hlen]
  right_inv q := by
    obtain ⟨⟨Q, hQ⟩, ⟨w, hw⟩⟩ := q
    have hcat : w.take (sizeTab Q₁) ++ w.drop (sizeTab Q₁) = w := List.take_append_drop _ _
    have hQw : RSQ w = Q := mem_langQ.1 hw
    refine Sigma.subtype_ext (Subtype.ext ?_) ?_
    · simp only [hcat, hQw]
    · simp only [hcat]

/-- **The free Littlewood–Richardson rule, as an identity between languages** (Coq
`free_LR_rule`): the concatenation of the languages of `Q₁` and `Q₂` is the union of the
languages of the tableaux completing them into a Littlewood–Richardson triple. -/
theorem catLang_langQ (hQ₁ : IsStdTab Q₁) :
    catLang (langQ σ Q₁) (langQ σ Q₂) = {w | ∃ Q, LRtriple Q₁ Q₂ Q ∧ w ∈ langQ σ Q} := by
  ext w
  rw [mem_catLang]
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    exact (LRrule_langQ hQ₁ _).1 ⟨u, v, rfl, hu, hv⟩
  · intro h
    obtain ⟨u, v, rfl, hu, hv⟩ := (LRrule_langQ hQ₁ w).2 h
    exact ⟨u, hu, v, hv, rfl⟩

/-- **The Littlewood–Richardson rule for tableaux** (Coq `LR_rule_tab`): the product of the
Schur polynomials of the shapes of two standard tableaux is the sum of the Schur polynomials
of the shapes of the standard tableaux completing them into a Littlewood–Richardson
triple. -/
theorem schurPoly_mul_eq_sum_LRtriple [Fintype σ] (hQ₁ : IsStdTab Q₁) (hQ₂ : IsStdTab Q₂) :
    schurPoly σ R (shape Q₁) * schurPoly σ R (shape Q₂)
      = ∑ Q : LRsupport Q₁ Q₂, schurPoly σ R (shape Q.1) := by
  classical
  rw [schurPoly_eq_sum_langQ (R := R) hQ₁, schurPoly_eq_sum_langQ (R := R) hQ₂,
    Finset.sum_mul_sum]
  have hright : ∑ Q : LRsupport Q₁ Q₂, schurPoly σ R (shape Q.1)
      = ∑ q : Σ Q : LRsupport Q₁ Q₂, langQ σ Q.1,
          ((q.2.1.map (X : σ → MvPolynomial σ R)).prod) := by
    rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
    exact Finset.sum_congr rfl fun Q _ => schurPoly_eq_sum_langQ (R := R) Q.2.1.1
  have hleft : ∑ i : langQ σ Q₁, ∑ j : langQ σ Q₂,
        ((i.1.map (X : σ → MvPolynomial σ R)).prod * (j.1.map (X : σ → MvPolynomial σ R)).prod)
      = ∑ p : langQ σ Q₁ × langQ σ Q₂,
          (((p.1.1 ++ p.2.1).map (X : σ → MvPolynomial σ R)).prod) := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      simp [List.map_append, List.prod_append]
  rw [hright, hleft]
  exact Fintype.sum_equiv (langQProdEquivSigma hQ₁ hQ₂) _ _ fun _ => rfl

end MvPolynomial
