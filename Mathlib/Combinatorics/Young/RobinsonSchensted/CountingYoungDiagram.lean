/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.RobinsonSchensted.Counting
public import Mathlib.Combinatorics.Young.HookLength.HookYoungDiagram
public import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram

/-!
# The identity `∑_λ (f^λ)² = n!` for partitions and Young diagrams

`Mathlib.Combinatorics.Young.RobinsonSchensted.Counting` proves the classical enumeration
`∑_λ (f^λ)² = n!` with the shapes `λ` given as weakly decreasing lists.  This file restates
it with the bundled types: the sum runs over `Nat.Partition n`, respectively over the Young
diagrams with `n` boxes, and `f^λ` is `YoungDiagram.numStdTab`.

## Main results

* `Nat.Partition.numStdTab_youngDiagram` : the number of standard tableaux of the diagram of a
  partition is the number of standard tableaux of its list of parts.
* `Nat.Partition.sum_sq_numStdTab` : `∑_λ (f^λ)² = n!`, summed over the partitions of `n`.
* `YoungDiagram.sum_sq_numStdTab` : `∑_λ (f^λ)² = n!`, summed over the Young diagrams with
  `n` boxes.
-/

@[expose] public section

open List Young

namespace Nat.Partition

variable {n : ℕ}

/-- The number of standard Young tableaux of the diagram of a partition is the number of
standard Young tableaux of its list of parts. -/
@[simp] lemma numStdTab_youngDiagram (p : Partition n) :
    p.youngDiagram.numStdTab = Young.numStdTab p.partsList := by
  rw [YoungDiagram.numStdTab, rowLens_youngDiagram]

/-- **`∑_λ (f^λ)² = n!`**: the sum, over the partitions `λ` of `n`, of the squares of the
numbers of standard Young tableaux of shape `λ`, is `n!`. -/
theorem sum_sq_numStdTab (n : ℕ) :
    ∑ p : Partition n, p.youngDiagram.numStdTab ^ 2 = Nat.factorial n := by
  simpa using Young.sum_sq_numStdTab n

end Nat.Partition

namespace YoungDiagram

/-- The Young diagrams with `n` boxes form a finite type: they are the partitions of `n`. -/
instance fintypeCardEq (n : ℕ) : Fintype {μ : YoungDiagram // μ.card = n} :=
  Fintype.ofEquiv _ (Nat.Partition.equivYoungDiagramCard n)

/-- **`∑_λ (f^λ)² = n!`**: the sum, over the Young diagrams `λ` with `n` boxes, of the squares
of the numbers of standard Young tableaux of shape `λ`, is `n!`. -/
theorem sum_sq_numStdTab (n : ℕ) :
    ∑ μ : {μ : YoungDiagram // μ.card = n}, (μ : YoungDiagram).numStdTab ^ 2 =
      Nat.factorial n := by
  rw [← Nat.Partition.sum_sq_numStdTab n]
  exact (Fintype.sum_equiv (Nat.Partition.equivYoungDiagramCard n) _ _ fun p => by
    rw [Nat.Partition.equivYoungDiagramCard_apply]).symm

end YoungDiagram
