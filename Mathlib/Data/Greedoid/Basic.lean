/-
Copyright (c) 2024 Jihoon Hyun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jihoon Hyun
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Greedoid.Predefs

/-!
# Greedoid

-/

structure Greedoid (α : Type _) [DecidableEq α] [Fintype α] where
  feasibleSet : Finset (Finset α)
  containsEmpty : ∅ ∈ feasibleSet
  accessibleProperty : Greedoid.AccessibleProperty feasibleSet
  exchangeProperty : Greedoid.ExchangeProperty feasibleSet

section Greedoid

variable {α : Type _} [DecidableEq α] [Fintype α]

/-- Definition of `Finset` in `Greedoid`.
    This is often called `feasible`. -/
protected def Greedoid.mem (s : Finset α) (G : Greedoid α) := s ∈ G.feasibleSet

instance : Membership (Finset α) (Greedoid α) := ⟨Greedoid.mem⟩

instance {G : Greedoid α} :
    DecidablePred (fun s => s ∈ G) := fun s =>
  if h : s ∈ G.feasibleSet
  then isTrue h
  else isFalse fun h' => h h'

end Greedoid

namespace Greedoid

variable {α : Type _} [DecidableEq α] [Fintype α] {G : Greedoid α}

open Nat List Finset

theorem eq_of_veq : ∀ {G₁ G₂ : Greedoid α},
  G₁.feasibleSet = G₂.feasibleSet → G₁ = G₂
  | ⟨Sys₁, _, _, _⟩, ⟨Sys₂, _, _, _⟩, h => by cases h; rfl

theorem feasibleSet_injective :
    Function.Injective (feasibleSet : Greedoid α → Finset (Finset α)) :=
  fun _ _ => eq_of_veq

@[simp]
theorem feasibleSet_inj {G₁ G₂ : Greedoid α} :
    G₁.feasibleSet = G₂.feasibleSet ↔ G₁ = G₂ :=
  feasibleSet_injective.eq_iff

instance : DecidableEq (Greedoid α) := fun G₁ G₂ =>
  if h : G₁.feasibleSet = G₂.feasibleSet
  then isTrue (eq_of_veq h)
  else isFalse (fun h' => h (h' ▸ rfl))

instance : Fintype (Greedoid α) where
  elems := ((@Finset.univ (Finset (Finset α)) _).filter fun Sys =>
    ∅ ∈ Sys ∧
    ({s : Finset α} → s ∈ Sys → s ≠ ∅ → ∃ x ∈ s, s \ {x} ∈ Sys) ∧
    ExchangeProperty Sys).attach.map ⟨fun Sys => ⟨Sys.val, by
      let ⟨val, prop⟩ := Sys; simp only; simp at prop; exact prop.1, fun h₁ h₂ => by
      let ⟨val, prop⟩ := Sys; simp only; simp at prop h₁; exact prop.2.1 h₁ h₂,
      fun {_} a {_} b c => by
      let ⟨val, prop⟩ := Sys; simp only; simp at prop a b; exact prop.2.2 a b c⟩,
    fun S₁ S₂ hS => by simp only [Greedoid.mk.injEq] at hS; exact Subtype.ext hS⟩
  complete G := by
    simp; exists G.feasibleSet; simp only [exists_prop, and_true]
    exact ⟨G.containsEmpty, G.accessibleProperty, G.exchangeProperty⟩

instance : Accessible G.feasibleSet := ⟨G.accessibleProperty⟩

section Membership

@[simp]
theorem system_feasible_set_mem_mem {s : Finset α} : s ∈ G.feasibleSet ↔ s ∈ G := by rfl

theorem emptyset_mem : ∅ ∈ G := G.containsEmpty

theorem mem_accessible {s : Finset α} (hs₁ : s ∈ G.feasibleSet) (hs₂ : s ≠ ∅) :
    ∃ x ∈ s, s \ {x} ∈ G.feasibleSet :=
  G.accessibleProperty hs₁ hs₂

theorem mem_exchangeAxiom
  {s₁ : Finset α} (hs₁ : s₁ ∈ G) {s₂ : Finset α} (hs₂ : s₂ ∈ G) (hs : s₂.card < s₁.card) :
    ∃ x ∈ s₁ \ s₂, insert x s₂ ∈ G :=
  G.exchangeProperty hs₁ hs₂ hs

end Membership

@[simp]
theorem feasibleSet_nonempty : G.feasibleSet.Nonempty := ⟨∅, G.containsEmpty⟩

-- Possible typo at IV· Lemma 1.5
/-- Normal greedoid contains no loops· -/
class Normal (G : Greedoid α) : Prop where
  /-- Loops are elements of the ground set which is not contained in any feasible set· -/
  noLoops : {a : α} → ∃ s, s ∈ G ∧ a ∈ s

/-- `Greedoid` is full if the ground set is feasible· -/
class Full (G : Greedoid α) : Prop where
  /-- Full greedoids contain its ground· -/
  full : univ ∈ G

/-- The interval property is satisfied by matroids, antimatroids, and some greedoids· -/
class IntervalProperty (G : Greedoid α) : Prop where
  /-- If there are three intervals A ⊆ B ⊆ C and
      some x which A ∪ {x} and C ∪ {x} are both intervals,
      then B ∪ {x} is also an interval· -/
  intervalProperty : {A : Finset α} → A ∈ G →
                     {B : Finset α} → B ∈ G →
                     {C : Finset α} → C ∈ G →
                     A ⊆ B → B ⊆ C → {x : α} → x ∉ C →
                     insert x A ∈ G → insert x C ∈ G → insert x B ∈ G

/-- (Finite) Matroid is an interval greedoid without lower bound· -/
class IntervalPropertyWithoutLowerBound (G : Greedoid α) : Prop where
  /-- If there are two intervals A ⊆ B and
      some x ∉ B which B ∪ {x} is an interval,
      then A ∪ {x} is also an interval· -/
  intervalPropertyWOLowerBound : {A : Finset α} → A ∈ G →
                                 {B : Finset α} → B ∈ G → A ⊆ B →
                                 {x : α} → x ∉ B →
                                 insert x B ∈ G → insert x A ∈ G

instance [IntervalPropertyWithoutLowerBound G] : IntervalProperty G where
  intervalProperty := by
    intro _ _ _ hB _ hC _ h₂ _ hx _ hCx
    exact IntervalPropertyWithoutLowerBound.intervalPropertyWOLowerBound hB hC h₂ hx hCx

/-- (Finite) Antimatroid is an interval greedoid without upper bound· -/
class IntervalPropertyWithoutUpperBound (G : Greedoid α) : Prop where
  /-- If there are two intervals B ⊆ A and
      some x ∉ A which B ∪ {x} is an interval,
      then A ∪ {x} is also an interval· -/
  intervalPropertyWOUpperBound : {A : Finset α} → A ∈ G →
                                 {B : Finset α} → B ∈ G → B ⊆ A →
                                 {x : α} → x ∉ A →
                                 insert x B ∈ G → insert x A ∈ G

instance [IntervalPropertyWithoutUpperBound G] : IntervalProperty G where
  intervalProperty := by
    intro _ hA _ hB _ _ h₁ h₂ _ hx hAx _
    exact IntervalPropertyWithoutUpperBound.intervalPropertyWOUpperBound
      hB hA h₁ (fun h => hx (h₂ h)) hAx

end Greedoid
