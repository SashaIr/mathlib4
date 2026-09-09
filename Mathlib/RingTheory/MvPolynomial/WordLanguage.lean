/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Fintype.Sets

/-!
# The generating polynomial of a language of words

A Lean 4 port of the generic machinery on languages of `theories/LRrule/freeSchur.v` from
[Coq-Combi](https://github.com/math-comp/Coq-Combi).

A *language* over an alphabet `σ` is a set of words `L : Set (List σ)`.  The *commutative
image* of a word is the monomial `∏ i ∈ w, X i`, and the *generating polynomial* of a finite
language is the sum of the commutative images of its words.  Concatenating two languages
multiplies their generating polynomials, provided the words of the first one all have the
same length, so that a word of the concatenation splits in only one way.

## Main definitions

* `MvPolynomial.commWord R w` : the commutative image `∏ i ∈ w, X i` of the word `w`
  (Coq `commword`).
* `MvPolynomial.polyLang R L` : the generating polynomial of the finite language `L`
  (Coq `polylang`).
* `MvPolynomial.IsHomLang d L` : all the words of `L` have length `d` (Coq `homlang`).
* `MvPolynomial.catLang L₁ L₂` : the concatenation of two languages (Coq `catlang`).

## Main results

* `MvPolynomial.catLangEquiv` : concatenation is a bijection from the pairs of words of two
  languages onto their concatenation, as soon as the first language is homogeneous.
* `MvPolynomial.polyLang_catLang` : **the generating polynomial of a concatenation is the
  product of the generating polynomials** (Coq `polylang_catlang`).
-/

namespace MvPolynomial

variable {σ : Type*} {R : Type*} [CommSemiring R]

/-! ### The commutative image of a word -/

/-- The commutative image of a word: the monomial `∏ i ∈ w, X i` (Coq `commword`). -/
noncomputable def commWord (R : Type*) [CommSemiring R] (w : List σ) : MvPolynomial σ R :=
  (w.map X).prod

@[simp] lemma commWord_nil : commWord R ([] : List σ) = 1 := rfl

@[simp] lemma commWord_cons (a : σ) (w : List σ) :
    commWord R (a :: w) = X a * commWord R w := rfl

/-- The commutative image of a concatenation is the product of the commutative images. -/
@[simp] lemma commWord_append (u v : List σ) :
    commWord R (u ++ v) = commWord R u * commWord R v := by
  simp [commWord, List.map_append, List.prod_append]

/-- Two words with the same letters have the same commutative image. -/
lemma commWord_of_perm {u v : List σ} (h : u.Perm v) : commWord R u = commWord R v :=
  (h.map (X : σ → MvPolynomial σ R)).prod_eq

/-! ### The generating polynomial of a language -/

/-- The generating polynomial of a finite language: the sum of the commutative images of its
words (Coq `polylang`). -/
noncomputable def polyLang (R : Type*) [CommSemiring R] (L : Set (List σ)) [Fintype L] :
    MvPolynomial σ R := ∑ w : L, commWord R w.1

/-- A language is *homogeneous of degree `d`* when all its words have length `d`
(Coq `homlang`). -/
def IsHomLang (d : ℕ) (L : Set (List σ)) : Prop := ∀ w ∈ L, List.length w = d

/-- The concatenation of two languages (Coq `catlang`). -/
def catLang (L₁ L₂ : Set (List σ)) : Set (List σ) := {w | ∃ u ∈ L₁, ∃ v ∈ L₂, w = u ++ v}

variable {L₁ L₂ : Set (List σ)}

lemma mem_catLang {w : List σ} :
    w ∈ catLang L₁ L₂ ↔ ∃ u ∈ L₁, ∃ v ∈ L₂, w = u ++ v := Iff.rfl

/-- Concatenation, as a map from the pairs of words of two languages to their
concatenation. -/
def catLangMap (L₁ L₂ : Set (List σ)) (p : L₁ × L₂) : catLang L₁ L₂ :=
  ⟨p.1.1 ++ p.2.1, p.1.1, p.1.2, p.2.1, p.2.2, rfl⟩

lemma catLangMap_surjective : Function.Surjective (catLangMap L₁ L₂) := by
  rintro ⟨w, u, hu, v, hv, rfl⟩
  exact ⟨(⟨u, hu⟩, ⟨v, hv⟩), rfl⟩

instance finite_catLang [Finite L₁] [Finite L₂] : Finite (catLang L₁ L₂) :=
  Finite.of_surjective _ (catLangMap_surjective (L₁ := L₁) (L₂ := L₂))

noncomputable instance fintype_catLang [Finite L₁] [Finite L₂] : Fintype (catLang L₁ L₂) :=
  Fintype.ofFinite _

/-- If all the words of the first language have the same length, a word of the concatenation
splits in only one way. -/
lemma catLangMap_injective {d : ℕ} (h : IsHomLang d L₁) :
    Function.Injective (catLangMap L₁ L₂) := by
  rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ ⟨⟨u', hu'⟩, ⟨v', hv'⟩⟩ he
  have he : u ++ v = u' ++ v' := congrArg Subtype.val he
  have hlen : u.length = u'.length := by rw [h u hu, h u' hu']
  obtain ⟨rfl, rfl⟩ := (List.append_inj he hlen)
  rfl

/-- **Concatenation is a bijection** from the pairs of words of two languages onto their
concatenation, as soon as the first language is homogeneous. -/
noncomputable def catLangEquiv {d : ℕ} (h : IsHomLang d L₁) : L₁ × L₂ ≃ catLang L₁ L₂ :=
  Equiv.ofBijective _ ⟨catLangMap_injective (L₂ := L₂) h, catLangMap_surjective⟩

/-- **The generating polynomial of a concatenation of languages is the product of their
generating polynomials** (Coq `polylang_catlang`). -/
theorem polyLang_catLang [Fintype L₁] [Fintype L₂] {d : ℕ} (h : IsHomLang d L₁) :
    polyLang R (catLang L₁ L₂) = polyLang R L₁ * polyLang R L₂ := by
  have hprod : polyLang R (catLang L₁ L₂)
      = ∑ p : L₁ × L₂, commWord R p.1.1 * commWord R p.2.1 := by
    refine (Fintype.sum_equiv (catLangEquiv (L₂ := L₂) h) _ _ fun p => ?_).symm
    change commWord R p.1.1 * commWord R p.2.1 =
      commWord R (p.1.1 ++ p.2.1)
    exact (commWord_append (R := R) p.1.1 p.2.1).symm
  rw [hprod, Fintype.sum_prod_type, polyLang, polyLang, Finset.sum_mul_sum]

end MvPolynomial
