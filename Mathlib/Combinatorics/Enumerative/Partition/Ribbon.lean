/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.List.Ribbon.Connected
public import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram

/-!
# Ribbons between partitions of an integer

`Mathlib.Combinatorics.Enumerative.Partition.List.Ribbon.Defs` defines a ribbon (or border
strip) for shapes given as weakly decreasing lists.  This file restates the definition for
partitions of an integer: `μ.IsRibbonOf ν` says that the skew shape `ν / μ` is a ribbon, and
`μ.ribbonHeight ν` is the number of rows it occupies.  This is the form in which ribbons enter
the Murnaghan–Nakayama rule.

## Main definitions

* `Nat.Partition.IsRibbonOf` : the skew shape `ν / μ` is a ribbon.
* `Nat.Partition.ribbonHeight` : the number of rows of the skew shape `ν / μ`.

## Main results

* `Nat.Partition.IsRibbonOf.le` : a ribbon shape contains the inner shape.
* `Nat.Partition.isRibbonOf_iff_isRibbon` : the textbook definition of a ribbon — nonempty,
  connected, without a `2 × 2` square — agrees with the operative one.
* `Nat.Partition.ribbonHeight_pos` : a ribbon occupies at least one row.
* `Nat.Partition.isRibbonOf_iff_rowLen_one_le` : a partition is a ribbon over the empty
  partition exactly when it is a hook.
* `Nat.Partition.ribbonHeight_of_isEmpty` : the height of a partition seen as a ribbon over
  the empty partition is its number of parts.
-/

@[expose] public section

open List Young

namespace Nat.Partition

variable {n N : ℕ}

/-- The skew shape `ν / μ` is a *ribbon* (or border strip): it occupies an interval of rows,
and each of its rows starts exactly one box to the left of where the previous one ended. -/
def IsRibbonOf (μ : Partition n) (ν : Partition N) : Prop :=
  ∃ start stop, RibbonOn start stop μ.partsList ν.partsList

/-- The number of rows occupied by the skew shape `ν / μ`. -/
def ribbonHeight (μ : Partition n) (ν : Partition N) : ℕ :=
  Young.ribbonHeight μ.partsList ν.partsList

lemma isRibbonOf_def (μ : Partition n) (ν : Partition N) :
    μ.IsRibbonOf ν ↔ ∃ start stop, RibbonOn start stop μ.partsList ν.partsList := Iff.rfl

lemma ribbonHeight_def (μ : Partition n) (ν : Partition N) :
    μ.ribbonHeight ν = Young.ribbonHeight μ.partsList ν.partsList := rfl

/-- A ribbon shape contains the inner shape. -/
theorem IsRibbonOf.le {μ : Partition n} {ν : Partition N} (h : μ.IsRibbonOf ν) :
    μ.youngDiagram ≤ ν.youngDiagram := by
  obtain ⟨start, stop, h⟩ := h
  exact (ofRowLens_le_iff_included (isPart_partsList μ) (isPart_partsList ν)).2
    (h.included (isPart_partsList μ))

/-- A ribbon has at least as many boxes outside as inside. -/
theorem IsRibbonOf.le_size {μ : Partition n} {ν : Partition N} (h : μ.IsRibbonOf ν) : n ≤ N := by
  have := Finset.card_le_card (show μ.youngDiagram.cells ⊆ ν.youngDiagram.cells from h.le)
  rwa [show μ.youngDiagram.cells.card = n from card_youngDiagram μ,
    show ν.youngDiagram.cells.card = N from card_youngDiagram ν] at this

/-- **The textbook definition of a ribbon agrees with the operative one**: a skew shape of
partitions is a ribbon exactly when it is nonempty, connected and contains no `2 × 2`
square. -/
theorem isRibbonOf_iff_isRibbon {μ : Partition n} {ν : Partition N}
    (hincl : μ.youngDiagram ≤ ν.youngDiagram) :
    μ.IsRibbonOf ν ↔ IsRibbon μ.partsList ν.partsList :=
  (isRibbon_iff_exists_ribbonOn (isPart_partsList μ) (isPart_partsList ν)
    ((ofRowLens_le_iff_included (isPart_partsList μ) (isPart_partsList ν)).1 hincl)).symm

/-- A ribbon occupies at least one row. -/
theorem ribbonHeight_pos {μ : Partition n} {ν : Partition N} (h : μ.IsRibbonOf ν) :
    0 < μ.ribbonHeight ν := by
  obtain ⟨start, stop, h⟩ := h
  rw [ribbonHeight_def, h.ribbonHeight_eq (isPart_partsList μ)]
  omega

/-- **A partition is a ribbon over the empty partition exactly when it is a hook**, that is
when its second row has at most one box. -/
theorem isRibbonOf_iff_rowLen_one_le (μ : Partition 0) {ν : Partition N} (hN : N ≠ 0) :
    μ.IsRibbonOf ν ↔ ν.youngDiagram.rowLen 1 ≤ 1 := by
  rw [isRibbonOf_def, rowLen_youngDiagram,
    show μ.partsList = [] from partsList_eq_nil_iff.2 rfl]
  exact exists_ribbonOn_nil_iff (isPart_partsList ν) (fun h => hN (partsList_eq_nil_iff.1 h))

/-- The height of a partition seen as a ribbon over the empty partition is its number of
parts. -/
theorem ribbonHeight_of_isEmpty (μ : Partition 0) (ν : Partition N) :
    μ.ribbonHeight ν = Multiset.card ν.parts := by
  rw [ribbonHeight_def, show μ.partsList = [] from partsList_eq_nil_iff.2 rfl,
    Young.ribbonHeight_nil (isPart_partsList ν), length_partsList]

end Nat.Partition
