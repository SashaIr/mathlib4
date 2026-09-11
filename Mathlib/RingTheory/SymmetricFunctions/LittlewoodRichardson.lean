/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.LittlewoodRichardson.YoungDiagram
public import Mathlib.RingTheory.SymmetricFunctions.Basic

/-!
# The Littlewood–Richardson rule for symmetric functions, with Young diagrams

`SymFunc.schurFunc_mul_schurFunc` of `Mathlib/RingTheory/SymmetricFunctions/Basic.lean`
expands a product of two Schur functions in the Schur basis, with the Littlewood–Richardson
coefficients of the lists of parts of the three partitions.  This file restates it with
`YoungDiagram.lrCoeff`, the coefficient of the three Young diagrams.

## Main results

* `SymFunc.schurFunc_mul_schurFunc_youngDiagram` : **the Littlewood–Richardson rule**,
  `s_μ · s_ν = ∑_ρ c^ρ_{μν} s_ρ`, with the coefficients of the Young diagrams of the
  partitions.

## References

* [I. G. Macdonald, *Symmetric functions and Hall polynomials*][macdonald1995]
* [F. Hivert et al., *Coq-Combi*][hivert-coqcombi]
-/

@[expose] public section

namespace SymFunc

variable {n : ℕ} {R : Type*} [CommRing R]

/-- **The Littlewood–Richardson rule for symmetric functions**, with the shapes given as
Young diagrams: the product of two Schur functions is the sum, over the partitions `ρ` of
`|μ| + |ν|`, of `c^ρ_{μν}` copies of the Schur function of shape `ρ`. -/
theorem schurFunc_mul_schurFunc_youngDiagram {a b : ℕ} (hab : a + b = n) (μ : Nat.Partition a)
    (ν : Nat.Partition b) :
    (schurFunc a R μ).1 * (schurFunc b R ν).1
      = ∑ ρ : Nat.Partition n,
          YoungDiagram.lrCoeff μ.youngDiagram ν.youngDiagram ρ.youngDiagram •
            (schurFunc n R ρ).1 := by
  rw [schurFunc_mul_schurFunc hab]
  exact Finset.sum_congr rfl fun ρ _ => by rw [YoungDiagram.lrCoeff_youngDiagram]

end SymFunc
