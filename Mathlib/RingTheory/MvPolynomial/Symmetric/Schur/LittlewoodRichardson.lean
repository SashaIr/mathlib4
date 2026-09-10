/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.LittlewoodRichardson.Rule
public import Mathlib.Combinatorics.Young.RobinsonSchensted.AlphabetMap
public import Mathlib.Combinatorics.Young.Shape.NatPartitionConj
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.Symmetric

/-!
# The Littlewood–Richardson rule for Schur polynomials

Combining the combinatorial Littlewood–Richardson rule of
`Mathlib/Combinatorics/Young/LittlewoodRichardson/Rule.lean` with the tableau definition of
the Schur polynomials gives the classical product formula

`s_λ · s_μ = ∑_ν c^ν_{λμ} · s_ν`,

the sum being over the partitions `ν` of `|λ| + |μ|` and `c^ν_{λμ}` being the
Littlewood–Richardson coefficient `Young.lrCoeff`.

## Main results

* `MvPolynomial.card_prodFiber_eq_lrCoeff` : over the alphabet `Fin m`, the number of pairs of
  tableaux of shapes `η` and `μ` with a given plactic product is the Littlewood–
  Richardson coefficient of the shape of that product.
* `MvPolynomial.schurPoly_mul_schurPoly` : the Littlewood–Richardson rule
  `s_λ · s_μ = ∑_ν c^ν_{λμ} · s_ν`.
-/

@[expose] public section

open Young

namespace MvPolynomial

open List MvPolynomial

variable {m : ℕ}

/-! ### Transfer of the pairs of tableaux to the alphabet `Fin m` -/

/-- The pairs of tableaux over `Fin m` of shapes `η` and `μ` whose plactic product is a
given tableau `V`. -/
def prodFiber (m : ℕ) (η μ : List ℕ) (V : List (List (Fin m))) : Type :=
  {q : SSYT (Fin m) η × SSYT (Fin m) μ // RS (toWord q.1.1 ++ toWord q.2.1) = V}

/-- A letter of a tableau over `ℕ` is a letter of its reading word. -/
lemma mem_toWord_of_mem_flatten {T : Type*} {A : List (List T)} {x : T} (h : x ∈ A.flatten) :
    x ∈ toWord A := by
  obtain ⟨r, hr, hx⟩ := List.mem_flatten.1 h
  exact mem_toWord.2 ⟨r, hr, hx⟩

/-- Every letter of a pair of tableaux over `ℕ` whose plactic product comes from the
alphabet `Fin m` is itself `< m`. -/
lemma lt_of_mem_flatten_of_RS_eq {A B : List (List ℕ)} {V : List (List (Fin m))}
    (h : RS (toWord A ++ toWord B) = mapTab Fin.val V) :
    (∀ x ∈ A.flatten, x < m) ∧ (∀ x ∈ B.flatten, x < m) := by
  have hperm := perm_toWord_RS (toWord A ++ toWord B)
  rw [h, toWord_mapTab] at hperm
  have hkey : ∀ x ∈ toWord A ++ toWord B, x < m := by
    intro x hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 (hperm.mem_iff.2 hx)
    exact j.2
  exact ⟨fun x hx => hkey x (List.mem_append_left _ (mem_toWord_of_mem_flatten hx)),
    fun x hx => hkey x (List.mem_append_right _ (mem_toWord_of_mem_flatten hx))⟩

/-- The image under `Fin.val` of a pair of tableaux over `Fin m` with plactic product
`V`. -/
lemma mapTab_val_mem_lrPairs {η μ : List ℕ} {V : List (List (Fin m))}
    (q : prodFiber m η μ V) :
    (mapTab Fin.val q.1.1.1, mapTab Fin.val q.1.2.1) ∈ lrPairs η μ (mapTab Fin.val V) := by
  refine ⟨isTableau_mapTab_val q.1.1.2.1, by rw [shape_mapTab, q.1.1.2.2],
    isTableau_mapTab_val q.1.2.2.1, by rw [shape_mapTab, q.1.2.2.2], ?_⟩
  rw [toWord_mapTab, toWord_mapTab, ← List.map_append, RS_map Fin.val_strictMono, q.2]

/-- Transfer of the pairs of tableaux from the alphabet `Fin m` to the alphabet `ℕ`. -/
lemma card_prodFiber_eq_ncard_lrPairs (η μ : List ℕ) (V : List (List (Fin m))) :
    Nat.card (prodFiber m η μ V) = (lrPairs η μ (mapTab Fin.val V)).ncard := by
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_congr (Equiv.ofBijective
    (fun q : prodFiber m η μ V => ⟨_, mapTab_val_mem_lrPairs q⟩) ⟨?_, ?_⟩)
  · rintro ⟨⟨⟨S, hS⟩, ⟨T, hT⟩⟩, hq⟩ ⟨⟨⟨S', hS'⟩, ⟨T', hT'⟩⟩, hq'⟩
    intro heq
    have h1 : mapTab (Fin.val : Fin m → ℕ) S = mapTab Fin.val S' :=
      congrArg (fun p => p.1.1) heq
    have h2 : mapTab (Fin.val : Fin m → ℕ) T = mapTab Fin.val T' :=
      congrArg (fun p => p.1.2) heq
    have hS'' := mapTab_injective (Fin.val_injective (n := m)) h1
    have hT'' := mapTab_injective (Fin.val_injective (n := m)) h2
    subst hS''; subst hT''; rfl
  · rintro ⟨⟨A, B⟩, hA, hνA, hB, hνB, hRS⟩
    obtain ⟨hboundA, hboundB⟩ := lt_of_mem_flatten_of_RS_eq hRS
    obtain ⟨A', hA'⟩ := exists_mapTab_val hboundA
    obtain ⟨B', hB'⟩ := exists_mapTab_val hboundB
    subst hA'; subst hB'
    have hRS' : RS (toWord A' ++ toWord B') = V := by
      apply mapTab_injective (Fin.val_injective (n := m))
      rw [← RS_map Fin.val_strictMono, List.map_append, ← toWord_mapTab, ← toWord_mapTab]
      exact hRS
    refine ⟨⟨(⟨A', isTableau_of_isTableau_mapTab Fin.val_strictMono hA,
      by rw [← shape_mapTab (Fin.val : Fin m → ℕ) A', hνA]⟩,
      ⟨B', isTableau_of_isTableau_mapTab Fin.val_strictMono hB,
      by rw [← shape_mapTab (Fin.val : Fin m → ℕ) B', hνB]⟩), hRS'⟩, rfl⟩

/-- Over the alphabet `Fin m`, the number of pairs of tableaux of shapes `η` and `μ`
whose plactic product is a given tableau `V` is the Littlewood–Richardson coefficient
`c^{shape V}_{η μ}`. -/
theorem card_prodFiber_eq_lrCoeff (η μ : List ℕ) {V : List (List (Fin m))}
    (hV : IsTableau V) :
    Nat.card (prodFiber m η μ V) = lrCoeff η μ (shape V) := by
  rw [card_prodFiber_eq_ncard_lrPairs, ncard_lrPairs_eq_lrCoeff (isTableau_mapTab_val hV),
    shape_mapTab]

/-! ### The product of two Schur polynomials -/

variable {R : Type*} [CommSemiring R]

/-- The shape of the plactic product of a pair of tableaux of shapes `η` and `μ`, as a
partition of `η.sum + μ.sum`. -/
def prodShape (η μ : List ℕ) (q : SSYT (Fin m) η × SSYT (Fin m) μ) :
    Nat.Partition (η.sum + μ.sum) :=
  listPartEquivNatPartition _ ⟨shape (RS (toWord q.1.1 ++ toWord q.2.1)),
    isPart_shape (isTableau_RS _), by
      rw [← sizeTab, sizeTab_RS, List.length_append, length_toWord, length_toWord,
        sizeTab, sizeTab, q.1.2.2, q.2.2.2]⟩

/-- The parts of the product shape are the shape of the plactic product. -/
lemma partsList_prodShape (η μ : List ℕ) (q : SSYT (Fin m) η × SSYT (Fin m) μ) :
    (prodShape η μ q).partsList = shape (RS (toWord q.1.1 ++ toWord q.2.1)) :=
  sortDesc_coe (isPart_shape (isTableau_RS _))

/-- A pair of tableaux has prescribed product shape exactly when the shape of its plactic
product is the corresponding list of parts. -/
lemma prodShape_eq_iff (η μ : List ℕ) (q : SSYT (Fin m) η × SSYT (Fin m) μ)
    (ν : Nat.Partition (η.sum + μ.sum)) :
    prodShape η μ q = ν ↔ shape (RS (toWord q.1.1 ++ toWord q.2.1)) = ν.partsList := by
  constructor
  · intro h; rw [← partsList_prodShape η μ q, h]
  · intro h
    refine Nat.Partition.ext ?_
    rw [← Nat.Partition.coe_partsList ν, ← h, ← partsList_prodShape η μ q,
      Nat.Partition.coe_partsList]

/-- **The Littlewood–Richardson rule**: the product of two Schur polynomials is the sum,
over the partitions `ν` of `|η| + |μ|`, of `c^ν_{η μ}` copies of the Schur
polynomial of shape `ν`. -/
theorem schurPoly_mul_schurPoly (η μ : List ℕ) :
    schurPoly (Fin m) R η * schurPoly (Fin m) R μ
      = ∑ ν : Nat.Partition (η.sum + μ.sum),
          lrCoeff η μ ν.partsList • schurPoly (Fin m) R ν.partsList := by
  classical
  have hLHS : schurPoly (Fin m) R η * schurPoly (Fin m) R μ
      = ∑ q : SSYT (Fin m) η × SSYT (Fin m) μ,
        ((toWord (RS (toWord q.1.1 ++ toWord q.2.1))).map
          (X : Fin m → MvPolynomial (Fin m) R)).prod := by
    rw [schurPoly, schurPoly, Finset.sum_mul_sum]
    conv_rhs => rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun T _ => ?_
    rw [← List.prod_append, ← List.map_append]
    exact (List.Perm.prod_eq ((perm_toWord_RS _).map _)).symm
  rw [hLHS, ← Fintype.sum_fiberwise (prodShape η μ)
    (fun q => ((toWord (RS (toWord q.1.1 ++ toWord q.2.1))).map
      (X : Fin m → MvPolynomial (Fin m) R)).prod)]
  refine Finset.sum_congr rfl fun ν _ => ?_
  set g : {q : SSYT (Fin m) η × SSYT (Fin m) μ // prodShape η μ q = ν} →
      SSYT (Fin m) ν.partsList := fun p =>
    ⟨RS (toWord p.1.1.1 ++ toWord p.1.2.1), isTableau_RS _,
      (prodShape_eq_iff η μ p.1 ν).1 p.2⟩
  rw [← Fintype.sum_fiberwise g
    (fun p => ((toWord (RS (toWord p.1.1.1 ++ toWord p.1.2.1))).map
      (X : Fin m → MvPolynomial (Fin m) R)).prod), schurPoly, Finset.smul_sum]
  refine Finset.sum_congr rfl fun V _ => ?_
  have hequiv : {p : {q : SSYT (Fin m) η × SSYT (Fin m) μ // prodShape η μ q = ν} //
      g p = V} ≃ prodFiber m η μ V.1 :=
    { toFun := fun p => ⟨p.1.1, congrArg Subtype.val p.2⟩
      invFun := fun q => ⟨⟨q.1, (prodShape_eq_iff η μ q.1 ν).2 (by rw [q.2, V.2.2])⟩,
        Subtype.ext q.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcard : Fintype.card {p : {q : SSYT (Fin m) η × SSYT (Fin m) μ //
      prodShape η μ q = ν} // g p = V} = lrCoeff η μ ν.partsList := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr hequiv,
      card_prodFiber_eq_lrCoeff η μ V.2.1, V.2.2]
  have hterm : ∀ p ∈ (Finset.univ : Finset {p : {q : SSYT (Fin m) η × SSYT (Fin m) μ //
        prodShape η μ q = ν} // g p = V}),
      ((toWord (RS (toWord p.1.1.1.1 ++ toWord p.1.1.2.1))).map
        (X : Fin m → MvPolynomial (Fin m) R)).prod
      = ((toWord V.1).map (X : Fin m → MvPolynomial (Fin m) R)).prod := by
    intro p _
    rw [show RS (toWord p.1.1.1.1 ++ toWord p.1.1.2.1) = V.1 from congrArg Subtype.val p.2]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_univ, hcard]

end MvPolynomial
