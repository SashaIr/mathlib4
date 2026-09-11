/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram
public import Mathlib.Combinatorics.Young.LittlewoodRichardson.Rule

/-!
# Littlewood–Richardson coefficients of Young diagrams

`Mathlib.Combinatorics.Young.LittlewoodRichardson.Rule` defines the Littlewood–Richardson
coefficient `Young.lrCoeff` of three shapes given as weakly decreasing lists.  This file
restates it for Mathlib's bundled `YoungDiagram`: `YoungDiagram.lrCoeff μ ν ρ` is the
number of pairs of tableaux of shapes `μ` and `ν` whose plactic product is a fixed tableau
of shape `ρ`.

The two symmetries of the coefficients are proved through the theory of symmetric functions,
so their bundled statements are in
`Mathlib/RingTheory/MvPolynomial/Symmetric/Schur/LRSymmetryYoungDiagram.lean`.

## Main definitions

* `YoungDiagram.lrCoeff` : the Littlewood–Richardson coefficient `c^ρ_{μν}` of three Young
  diagrams.

## Main results

* `YoungDiagram.lrCoeff_eq_ncard_lrTableaux` : `c^ρ_{μν}` counts the tableaux of shape `μ`
  whose plactic product with the superstandard tableau of shape `ν` is superstandard of
  shape `ρ`.
* `YoungDiagram.lrCoeff_bot_right` : `c^μ_{μ, ∅} = 1`.
* `YoungDiagram.lrCoeff_youngDiagram` : it agrees with the coefficient of the underlying
  partitions of an integer.

## References

* [W. Fulton, *Young tableaux*][fulton1997]
* [I. G. Macdonald, *Symmetric functions and Hall polynomials*][macdonald1995]
* [F. Hivert et al., *Coq-Combi*][hivert-coqcombi]
-/

@[expose] public section

namespace YoungDiagram

open List Young

/-- The empty Young diagram has no rows. -/
@[simp] theorem rowLens_bot : (⊥ : YoungDiagram).rowLens = [] := by
  have hcol : (⊥ : YoungDiagram).colLen 0 = 0 := by
    by_contra h
    exact notMem_bot (0, 0) (mem_iff_lt_colLen.2 (Nat.pos_of_ne_zero h))
  exact List.eq_nil_of_length_eq_zero (by rw [length_rowLens, hcol])

/-- The Littlewood–Richardson coefficient `c^ρ_{μν}` of three Young diagrams: the number of
pairs of tableaux of shapes `μ` and `ν` whose plactic product is a fixed tableau of shape
`ρ`. -/
noncomputable def lrCoeff (μ ν ρ : YoungDiagram) : ℕ :=
  Young.lrCoeff μ.rowLens ν.rowLens ρ.rowLens

theorem lrCoeff_def (μ ν ρ : YoungDiagram) :
    lrCoeff μ ν ρ = Young.lrCoeff μ.rowLens ν.rowLens ρ.rowLens := rfl

/-- The Littlewood–Richardson coefficient `c^ρ_{μν}` counts the tableaux of shape `μ` whose
plactic product with the superstandard tableau of shape `ν` is the superstandard tableau of
shape `ρ`. -/
theorem lrCoeff_eq_ncard_lrTableaux (μ ν ρ : YoungDiagram) :
    lrCoeff μ ν ρ = (lrTableaux μ.rowLens ν.rowLens ρ.rowLens).ncard :=
  Young.lrCoeff_eq_ncard_lrTableaux (isPart_rowLens ν) (isPart_rowLens ρ)

/-- The number of pairs of tableaux of shapes `μ` and `ν` with a given plactic product `V`
only depends on the shape of `V`, and equals the Littlewood–Richardson coefficient. -/
theorem ncard_lrPairs_eq_lrCoeff {μ ν ρ : YoungDiagram} {V : List (List ℕ)}
    (hV : IsTableau V) (hshape : shape V = ρ.rowLens) :
    (lrPairs μ.rowLens ν.rowLens V).ncard = lrCoeff μ ν ρ := by
  rw [lrCoeff_def, ← hshape]
  exact Young.ncard_lrPairs_eq_lrCoeff hV

/-- Multiplying by the empty diagram does nothing: `c^μ_{μ, ∅} = 1`.  In particular the
Littlewood–Richardson coefficients are not all zero. -/
theorem lrCoeff_bot_right (μ : YoungDiagram) : lrCoeff μ ⊥ μ = 1 := by
  rw [lrCoeff_def, rowLens_bot]
  exact Young.lrCoeff_nil_right (isPart_rowLens μ)

/-- The Littlewood–Richardson coefficient of the diagrams of three partitions of an integer
is the Littlewood–Richardson coefficient of their lists of parts. -/
@[simp] theorem lrCoeff_youngDiagram {a b c : ℕ} (μ : Nat.Partition a) (ν : Nat.Partition b)
    (ρ : Nat.Partition c) :
    lrCoeff μ.youngDiagram ν.youngDiagram ρ.youngDiagram
      = Young.lrCoeff μ.partsList ν.partsList ρ.partsList := by
  rw [lrCoeff_def, Nat.Partition.rowLens_youngDiagram, Nat.Partition.rowLens_youngDiagram,
    Nat.Partition.rowLens_youngDiagram]

end YoungDiagram
