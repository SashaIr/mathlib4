/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.LittlewoodRichardson.Rule
public import Mathlib.Combinatorics.Young.RobinsonSchensted.AlphabetMap
public import Mathlib.Combinatorics.Enumerative.Partition.Conj
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.Symmetric

/-!
# The Littlewood–Richardson rule for Schur polynomials

Combining the combinatorial Littlewood–Richardson rule of
`Mathlib/Combinatorics/Young/LittlewoodRichardson/Rule.lean` with the tableau definition of
the Schur polynomials gives the classical product formula

`s_μ · s_ν = ∑_ρ c^ρ_{μν} · s_ρ`,

the sum being over the partitions `ρ` of `|μ| + |ν|` and `c^ρ_{μν}` being the
Littlewood–Richardson coefficient `Young.lrCoeff`.

## Main results

* `MvPolynomial.card_prodFiber_eq_lrCoeff` : over the alphabet `Fin m`, the number of pairs of
  tableaux of shapes `μ` and `ν` with a given plactic product is the Littlewood–
  Richardson coefficient of the shape of that product.
* `MvPolynomial.schurPoly_mul_schurPoly` : the Littlewood–Richardson rule
  `s_μ · s_ν = ∑_ρ c^ρ_{μν} · s_ρ`.
-/

@[expose] public section

open Young

namespace MvPolynomial

open List MvPolynomial

variable {m : ℕ}

/-! ### Transfer of the pairs of tableaux to the alphabet `Fin m` -/

/-- The pairs of tableaux over `Fin m` of shapes `μ` and `ν` whose plactic product is a
given tableau `V`. -/
def prodFiber (m : ℕ) (μ ν : List ℕ) (V : List (List (Fin m))) : Type :=
  {q : SSYT (Fin m) μ × SSYT (Fin m) ν // RS (toWord q.1.1 ++ toWord q.2.1) = V}

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
lemma mapTab_val_mem_lrPairs {μ ν : List ℕ} {V : List (List (Fin m))}
    (q : prodFiber m μ ν V) :
    (mapTab Fin.val q.1.1.1, mapTab Fin.val q.1.2.1) ∈ lrPairs μ ν (mapTab Fin.val V) := by
  refine ⟨isTableau_mapTab_val q.1.1.2.1, by rw [shape_mapTab, q.1.1.2.2],
    isTableau_mapTab_val q.1.2.2.1, by rw [shape_mapTab, q.1.2.2.2], ?_⟩
  rw [toWord_mapTab, toWord_mapTab, ← List.map_append, RS_map Fin.val_strictMono, q.2]

/-- Transfer of the pairs of tableaux from the alphabet `Fin m` to the alphabet `ℕ`. -/
lemma card_prodFiber_eq_ncard_lrPairs (μ ν : List ℕ) (V : List (List (Fin m))) :
    Nat.card (prodFiber m μ ν V) = (lrPairs μ ν (mapTab Fin.val V)).ncard := by
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_congr (Equiv.ofBijective
    (fun q : prodFiber m μ ν V => ⟨_, mapTab_val_mem_lrPairs q⟩) ⟨?_, ?_⟩)
  · rintro ⟨⟨⟨S, hS⟩, ⟨T, hT⟩⟩, hq⟩ ⟨⟨⟨S', hS'⟩, ⟨T', hT'⟩⟩, hq'⟩
    intro heq
    have h1 : mapTab (Fin.val : Fin m → ℕ) S = mapTab Fin.val S' :=
      congrArg (fun p => p.1.1) heq
    have h2 : mapTab (Fin.val : Fin m → ℕ) T = mapTab Fin.val T' :=
      congrArg (fun p => p.1.2) heq
    have hS'' := mapTab_injective (Fin.val_injective (n := m)) h1
    have hT'' := mapTab_injective (Fin.val_injective (n := m)) h2
    subst hS''; subst hT''; rfl
  · rintro ⟨⟨A, B⟩, hA, hρA, hB, hρB, hRS⟩
    obtain ⟨hboundA, hboundB⟩ := lt_of_mem_flatten_of_RS_eq hRS
    obtain ⟨A', hA'⟩ := exists_mapTab_val hboundA
    obtain ⟨B', hB'⟩ := exists_mapTab_val hboundB
    subst hA'; subst hB'
    have hRS' : RS (toWord A' ++ toWord B') = V := by
      apply mapTab_injective (Fin.val_injective (n := m))
      rw [← RS_map Fin.val_strictMono, List.map_append, ← toWord_mapTab, ← toWord_mapTab]
      exact hRS
    refine ⟨⟨(⟨A', isTableau_of_isTableau_mapTab Fin.val_strictMono hA,
      by rw [← shape_mapTab (Fin.val : Fin m → ℕ) A', hρA]⟩,
      ⟨B', isTableau_of_isTableau_mapTab Fin.val_strictMono hB,
      by rw [← shape_mapTab (Fin.val : Fin m → ℕ) B', hρB]⟩), hRS'⟩, rfl⟩

/-- Over the alphabet `Fin m`, the number of pairs of tableaux of shapes `μ` and `ν`
whose plactic product is a given tableau `V` is the Littlewood–Richardson coefficient
`c^{shape V}_{μ ν}`. -/
theorem card_prodFiber_eq_lrCoeff (μ ν : List ℕ) {V : List (List (Fin m))}
    (hV : IsTableau V) :
    Nat.card (prodFiber m μ ν V) = lrCoeff μ ν (shape V) := by
  rw [card_prodFiber_eq_ncard_lrPairs, ncard_lrPairs_eq_lrCoeff (isTableau_mapTab_val hV),
    shape_mapTab]

/-! ### The product of two Schur polynomials -/

variable {R : Type*} [CommSemiring R]

/-- The shape of the plactic product of a pair of tableaux of shapes `μ` and `ν`, as a
partition of `μ.sum + ν.sum`. -/
def prodShape (μ ν : List ℕ) (q : SSYT (Fin m) μ × SSYT (Fin m) ν) :
    Nat.Partition (μ.sum + ν.sum) :=
  listPartEquivNatPartition _ ⟨shape (RS (toWord q.1.1 ++ toWord q.2.1)),
    isPart_shape (isTableau_RS _), by
      rw [← sizeTab, sizeTab_RS, List.length_append, length_toWord, length_toWord,
        sizeTab, sizeTab, q.1.2.2, q.2.2.2]⟩

/-- The parts of the product shape are the shape of the plactic product. -/
lemma partsList_prodShape (μ ν : List ℕ) (q : SSYT (Fin m) μ × SSYT (Fin m) ν) :
    (prodShape μ ν q).partsList = shape (RS (toWord q.1.1 ++ toWord q.2.1)) :=
  sortDesc_coe (isPart_shape (isTableau_RS _))

/-- A pair of tableaux has prescribed product shape exactly when the shape of its plactic
product is the corresponding list of parts. -/
lemma prodShape_eq_iff (μ ν : List ℕ) (q : SSYT (Fin m) μ × SSYT (Fin m) ν)
    (ρ : Nat.Partition (μ.sum + ν.sum)) :
    prodShape μ ν q = ρ ↔ shape (RS (toWord q.1.1 ++ toWord q.2.1)) = ρ.partsList := by
  constructor
  · intro h; rw [← partsList_prodShape μ ν q, h]
  · intro h
    refine Nat.Partition.ext ?_
    rw [← Nat.Partition.coe_partsList ρ, ← h, ← partsList_prodShape μ ν q,
      Nat.Partition.coe_partsList]

/-- **The Littlewood–Richardson rule**: the product of two Schur polynomials is the sum,
over the partitions `ρ` of `|μ| + |ν|`, of `c^ρ_{μ ν}` copies of the Schur
polynomial of shape `ρ`. -/
theorem schurPoly_mul_schurPoly (μ ν : List ℕ) :
    schurPoly (Fin m) R μ * schurPoly (Fin m) R ν
      = ∑ ρ : Nat.Partition (μ.sum + ν.sum),
          lrCoeff μ ν ρ.partsList • schurPoly (Fin m) R ρ.partsList := by
  classical
  have hLHS : schurPoly (Fin m) R μ * schurPoly (Fin m) R ν
      = ∑ q : SSYT (Fin m) μ × SSYT (Fin m) ν,
        ((toWord (RS (toWord q.1.1 ++ toWord q.2.1))).map
          (X : Fin m → MvPolynomial (Fin m) R)).prod := by
    rw [schurPoly, schurPoly, Finset.sum_mul_sum]
    conv_rhs => rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun T _ => ?_
    rw [← List.prod_append, ← List.map_append]
    exact (List.Perm.prod_eq ((perm_toWord_RS _).map _)).symm
  rw [hLHS, ← Fintype.sum_fiberwise (prodShape μ ν)
    (fun q => ((toWord (RS (toWord q.1.1 ++ toWord q.2.1))).map
      (X : Fin m → MvPolynomial (Fin m) R)).prod)]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  set g : {q : SSYT (Fin m) μ × SSYT (Fin m) ν // prodShape μ ν q = ρ} →
      SSYT (Fin m) ρ.partsList := fun p =>
    ⟨RS (toWord p.1.1.1 ++ toWord p.1.2.1), isTableau_RS _,
      (prodShape_eq_iff μ ν p.1 ρ).1 p.2⟩
  rw [← Fintype.sum_fiberwise g
    (fun p => ((toWord (RS (toWord p.1.1.1 ++ toWord p.1.2.1))).map
      (X : Fin m → MvPolynomial (Fin m) R)).prod), schurPoly, Finset.smul_sum]
  refine Finset.sum_congr rfl fun V _ => ?_
  have hequiv : {p : {q : SSYT (Fin m) μ × SSYT (Fin m) ν // prodShape μ ν q = ρ} //
      g p = V} ≃ prodFiber m μ ν V.1 :=
    { toFun := fun p => ⟨p.1.1, congrArg Subtype.val p.2⟩
      invFun := fun q => ⟨⟨q.1, (prodShape_eq_iff μ ν q.1 ρ).2 (by rw [q.2, V.2.2])⟩,
        Subtype.ext q.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcard : Fintype.card {p : {q : SSYT (Fin m) μ × SSYT (Fin m) ν //
      prodShape μ ν q = ρ} // g p = V} = lrCoeff μ ν ρ.partsList := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr hequiv,
      card_prodFiber_eq_lrCoeff μ ν V.2.1, V.2.2]
  have hterm : ∀ p ∈ (Finset.univ : Finset {p : {q : SSYT (Fin m) μ × SSYT (Fin m) ν //
        prodShape μ ν q = ρ} // g p = V}),
      ((toWord (RS (toWord p.1.1.1.1 ++ toWord p.1.1.2.1))).map
        (X : Fin m → MvPolynomial (Fin m) R)).prod
      = ((toWord V.1).map (X : Fin m → MvPolynomial (Fin m) R)).prod := by
    intro p _
    rw [show RS (toWord p.1.1.1.1 ++ toWord p.1.1.2.1) = V.1 from congrArg Subtype.val p.2]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_univ, hcard]

end MvPolynomial
