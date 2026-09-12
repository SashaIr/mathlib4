/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.Tableau.Kostka
public import Mathlib.Combinatorics.Enumerative.Partition.Conj

/-!
# Kostka numbers of partitions of an integer

The Kostka number `Young.kostka` of `Mathlib.Combinatorics.Young.Tableau.Kostka` counts the
tableaux of a given shape and content, both given as weakly decreasing lists.  A shape and a
content of a tableau with `n` boxes are both partitions of `n`, so the Kostka number is
naturally a function of two elements of `Nat.Partition n`; that is the form given here.

## Main definitions

* `Nat.Partition.kostka` : the Kostka number of two partitions of `n`.

## Main results

* `Nat.Partition.kostka_self` : `K μ μ = 1`.
* `Nat.Partition.kostka_eq_zero_of_not_partdom` : `K μ ν = 0` unless `μ` dominates `ν`.
-/

@[expose] public section

open List Young

namespace Nat.Partition

variable {n : ℕ}

/-- The Kostka number `K μ ν` of two partitions of `n`: the number of semistandard Young
tableaux of shape `μ` and content `ν`. -/
noncomputable def kostka (μ ν : Partition n) : ℕ := Young.kostka μ.partsList ν.partsList

lemma kostka_def (μ ν : Partition n) : kostka μ ν = Young.kostka μ.partsList ν.partsList := rfl

/-- A Kostka number `K μ ν` vanishes unless the shape `μ` dominates the content `ν`. -/
theorem kostka_eq_zero_of_not_partdom {μ ν : Partition n} (h : ¬ Partdom ν μ) :
    kostka μ ν = 0 :=
  Young.kostka_eq_zero_of_not_partdom h

/-- The Kostka number `K μ μ` is `1`: the superstandard tableau is the unique tableau whose
content equals its shape. -/
theorem kostka_self (μ : Partition n) : kostka μ μ = 1 :=
  Young.kostka_self (isPart_partsList μ)

end Nat.Partition
