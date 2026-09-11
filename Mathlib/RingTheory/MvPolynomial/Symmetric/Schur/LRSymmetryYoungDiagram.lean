/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.LittlewoodRichardson.YoungDiagram
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.LRSymmetry

/-!
# Symmetries of the Littlewood–Richardson coefficients of Young diagrams

`Mathlib/RingTheory/MvPolynomial/Symmetric/Schur/LRSymmetry.lean` proves the two symmetries
of the Littlewood–Richardson coefficients for shapes given as weakly decreasing lists.  This
file restates them for `YoungDiagram.lrCoeff`, where conjugation of partitions is
`YoungDiagram.transpose` and the size of a shape is the number of its boxes.

## Main results

* `YoungDiagram.lrCoeff_comm` : `c^ρ_{μν} = c^ρ_{νμ}`.
* `YoungDiagram.lrCoeff_transpose` : `c^{ρᵀ}_{μᵀνᵀ} = c^ρ_{μν}`.

## References

* [W. Fulton, *Young tableaux*][fulton1997]
* [I. G. Macdonald, *Symmetric functions and Hall polynomials*][macdonald1995]
* [F. Hivert et al., *Coq-Combi*][hivert-coqcombi]
-/

@[expose] public section

namespace YoungDiagram

open Young

variable {μ ν ρ : YoungDiagram}

/-- **The Littlewood–Richardson coefficients are symmetric in their two lower indices.** -/
theorem lrCoeff_comm (h : ρ.card = μ.card + ν.card) : lrCoeff μ ν ρ = lrCoeff ν μ ρ :=
  MvPolynomial.lrCoeff_comm (isPart_rowLens ρ) (by
    rw [← card_eq_sum_rowLens, ← card_eq_sum_rowLens, ← card_eq_sum_rowLens]; exact h)

/-- **The Littlewood–Richardson coefficients are invariant under transposing all three
diagrams** (Coq `LRtab_coeff_conj`). -/
theorem lrCoeff_transpose (h : ρ.card = μ.card + ν.card) :
    lrCoeff μ.transpose ν.transpose ρ.transpose = lrCoeff μ ν ρ := by
  rw [lrCoeff_def, lrCoeff_def, rowLens_transpose, rowLens_transpose, rowLens_transpose]
  exact MvPolynomial.lrCoeff_conjPart (isPart_rowLens μ) (isPart_rowLens ν) (isPart_rowLens ρ)
    (by rw [← card_eq_sum_rowLens, ← card_eq_sum_rowLens, ← card_eq_sum_rowLens]; exact h)

end YoungDiagram
