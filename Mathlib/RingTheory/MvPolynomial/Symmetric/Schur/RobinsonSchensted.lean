/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.RobinsonSchensted.Counting
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.Basic

/-!
# The Robinson–Schensted expansion of a power of the sum of the variables

Refining the counting identity `∑_λ K_λ(m) · f^λ = m ^ n` of
`Mathlib/Combinatorics/Young/RobinsonSchensted/CountingWords.lean` at the level of monomials,
the Robinson–Schensted correspondence yields the polynomial identity

`(x_1 + ⋯ + x_m) ^ n = ∑_λ f^λ · s_λ`,

the sum being over the partitions `λ` of `n`, where `f^λ` is the number of standard
tableaux of shape `λ` and `s_λ` is the Schur polynomial of shape `λ`.

## Main results

* `MvPolynomial.sum_monomial_word` : `(∑ i, X i) ^ n` is the sum of the monomials of the words of
  length `n`.
* `MvPolynomial.sum_numStdTab_smul_schurPoly` : the identity `∑_λ f^λ · s_λ = (∑ i, X i) ^ n`.
-/

@[expose] public section

open Young

namespace MvPolynomial

open List MvPolynomial

/-! ### Standard tableaux of a given shape form a finite type -/

instance finite_stdTabOfShape (μ : List ℕ) :
    Finite {Q : List (List ℕ) // IsStdTab Q ∧ shape Q = μ} := by
  classical
  refine Finite.of_injective
    (fun Q : {Q : List (List ℕ) // IsStdTab Q ∧ shape Q = μ} =>
      (⟨Q.1.flatten, ?_⟩ : {w : List ℕ // w ∈ (List.range μ.sum).permutations})) ?_
  · refine List.mem_permutations.2 ?_
    have hstd : (toWord Q.1).Perm (List.range (toWord Q.1).length) := Q.2.1.2
    have hlen : (toWord Q.1).length = μ.sum := by
      rw [length_toWord, sizeTab, Q.2.2]
    have hperm : (Q.1.flatten).Perm (toWord Q.1) :=
      ((List.reverse_perm Q.1).flatten).symm
    rw [hlen] at hstd
    exact hperm.trans hstd
  · rintro ⟨P, hP⟩ ⟨Q, hQ⟩ h
    have hf : P.flatten = Q.flatten := congrArg Subtype.val h
    exact Subtype.ext (eq_of_shape_eq_of_flatten_eq (by rw [hP.2, hQ.2]) hf)

noncomputable instance fintypeStdTabOfShape (μ : List ℕ) :
    Fintype {Q : List (List ℕ) // IsStdTab Q ∧ shape Q = μ} :=
  Fintype.ofFinite _

lemma numStdTab_eq_card (μ : List ℕ) :
    numStdTab μ = Fintype.card {Q : List (List ℕ) // IsStdTab Q ∧ shape Q = μ} :=
  Nat.card_eq_fintype_card

/-! ### The monomials of the words of a given length -/

variable {σ : Type*} [Fintype σ] [LinearOrder σ] {R : Type*} [CommSemiring R]

omit [LinearOrder σ] in
/-- The `n`-th power of the sum of the variables is the sum of the monomials of the words
of length `n`. -/
theorem sum_monomial_word (n : ℕ) :
    ∑ v : List.Vector σ n, ((v.1.map (X : σ → MvPolynomial σ R)).prod) = (∑ i : σ, X i) ^ n := by
  rw [Fintype.sum_pow]
  refine Fintype.sum_equiv (Equiv.vectorEquivFin σ n) _ _ ?_
  intro v
  have hv : List.ofFn (Equiv.vectorEquivFin σ n v) = v.1 := by
    have h := congrArg List.Vector.toList (List.Vector.ofFn_get v)
    rw [List.Vector.toList_ofFn] at h
    exact h
  rw [← List.prod_ofFn]
  congr 1
  rw [← hv, List.map_ofFn]
  rfl

/-! ### The Robinson–Schensted correspondence on words of a given length -/

/-- The pairs consisting of a tableau over `σ` and a standard tableau of the same shape
with `n` boxes. -/
def tabPairS (σ : Type*) [LinearOrder σ] (n : ℕ) : Set (List (List σ) × List (List ℕ)) :=
  {p | IsTableau p.1 ∧ IsStdTab p.2 ∧ shape p.2 = shape p.1 ∧ sizeTab p.1 = n}

omit [Fintype σ] in
/-- The Robinson–Schensted correspondence is a bijection between the words of length `n`
over `σ` and the pairs consisting of a tableau over `σ` and a standard tableau of the same
shape with `n` boxes. -/
theorem RS_RSQ_bijOn_wordS (n : ℕ) :
    Set.BijOn (fun w : List σ => (RS w, RSQ w)) {w : List σ | w.length = n} (tabPairS σ n) := by
  have hbij := RS_RSQ_bijOn (T := σ)
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨h1, h2, h3⟩ := hbij.mapsTo (Set.mem_univ w)
    exact ⟨h1, h2, h3, by rw [sizeTab_RS, hw]⟩
  · exact hbij.injOn.mono (Set.subset_univ _)
  · rintro p ⟨h1, h2, h3, h4⟩
    obtain ⟨w, -, hfw⟩ := hbij.surjOn ⟨h1, h2, h3⟩
    have hlen : w.length = n := by
      have hp : RS w = p.1 := congrArg Prod.fst hfw
      rw [← sizeTab_RS w, hp, h4]
    exact ⟨w, hlen, hfw⟩

/-- The Robinson–Schensted correspondence, as an equivalence. -/
noncomputable def wordEquivTabPairS (n : ℕ) : List.Vector σ n ≃ tabPairS σ n :=
  (RS_RSQ_bijOn_wordS (σ := σ) n).equiv

omit [Fintype σ] in
instance finite_tabPairS [Finite σ] (n : ℕ) : Finite (tabPairS σ n) := by
  have : Fintype σ := Fintype.ofFinite σ
  exact Finite.of_equiv _ (wordEquivTabPairS (σ := σ) n)

noncomputable instance fintypeTabPairS (n : ℕ) : Fintype (tabPairS σ n) :=
  Fintype.ofFinite _

/-- The common shape of such a pair, as a partition of `n`. -/
def tabPairShapeS (n : ℕ) (p : tabPairS σ n) : Nat.Partition n :=
  listPartEquivNatPartition n ⟨shape p.1.1, isPart_shape p.2.1, p.2.2.2.2⟩

omit [Fintype σ] in
lemma partsList_tabPairShapeS (n : ℕ) (p : tabPairS σ n) :
    (tabPairShapeS n p).partsList = shape p.1.1 :=
  sortDesc_coe (isPart_shape p.2.1)

/-- The pairs with prescribed shape `η` are the pairs of a tableau over `σ` of shape
`η` and a standard tableau of shape `η`. -/
def tabPairSFiberEquiv (n : ℕ) (η : Nat.Partition n) :
    {p : tabPairS σ n // tabPairShapeS n p = η} ≃
      SSYT σ η.partsList × {Q : List (List ℕ) // IsStdTab Q ∧ shape Q = η.partsList} where
  toFun p :=
    have h1 : shape p.1.1.1 = η.partsList := by
      rw [← partsList_tabPairShapeS n p.1, p.2]
    (⟨p.1.1.1, p.1.2.1, h1⟩, ⟨p.1.1.2, p.1.2.2.1, by rw [p.1.2.2.2.1, h1]⟩)
  invFun q :=
    ⟨⟨(q.1.1, q.2.1), q.1.2.1, q.2.2.1, by rw [q.1.2.2, q.2.2.2], by
        change (shape q.1.1).sum = n
        rw [q.1.2.2, Nat.Partition.sum_partsList]⟩,
      Nat.Partition.ext (by
        change ((shape q.1.1 : List ℕ) : Multiset ℕ) = η.parts
        rw [q.1.2.2, Nat.Partition.coe_partsList])⟩
  left_inv p := rfl
  right_inv q := rfl

/-! ### The identity `∑_λ f^λ · s_λ = (x_1 + ⋯ + x_m) ^ n` -/

/-- **The Robinson–Schensted expansion**: the `n`-th power of the sum of the variables is
the sum, over the partitions `λ` of `n`, of `f^λ` copies of the Schur polynomial `s_λ`,
where `f^λ` is the number of standard tableaux of shape `λ`. -/
theorem sum_numStdTab_smul_schurPoly (n : ℕ) :
    ∑ η : Nat.Partition n, numStdTab η.partsList • schurPoly σ R η.partsList
      = (∑ i : σ, X i) ^ n := by
  classical
  rw [← sum_monomial_word (σ := σ) (R := R) n]
  have h1 : ∑ v : List.Vector σ n, ((v.1.map (X : σ → MvPolynomial σ R)).prod)
      = ∑ p : tabPairS σ n, ((toWord p.1.1).map (X : σ → MvPolynomial σ R)).prod := by
    refine Fintype.sum_equiv (wordEquivTabPairS (σ := σ) n) _ _ ?_
    intro v
    have hp : (toWord (RS v.1)).Perm v.1 := perm_toWord_RS v.1
    change (List.map (X : σ → MvPolynomial σ R) v.1).prod
        = (List.map (X : σ → MvPolynomial σ R) (toWord (RS v.1))).prod
    exact (List.Perm.prod_eq (hp.map (X : σ → MvPolynomial σ R))).symm
  rw [h1, ← Fintype.sum_fiberwise (tabPairShapeS (σ := σ) n)
    (fun p => ((toWord p.1.1).map (X : σ → MvPolynomial σ R)).prod)]
  refine Finset.sum_congr rfl fun η _ => ?_
  have h2 : ∑ p : {p : tabPairS σ n // tabPairShapeS n p = η},
        ((toWord p.1.1.1).map (X : σ → MvPolynomial σ R)).prod
      = ∑ q : SSYT σ η.partsList × {Q : List (List ℕ) // IsStdTab Q ∧ shape Q = η.partsList},
        ((toWord q.1.1).map (X : σ → MvPolynomial σ R)).prod :=
    Fintype.sum_equiv (tabPairSFiberEquiv (σ := σ) n η) _ _ (fun _ => rfl)
  rw [h2, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ]
  rw [schurPoly, Finset.smul_sum, numStdTab_eq_card]

end MvPolynomial
