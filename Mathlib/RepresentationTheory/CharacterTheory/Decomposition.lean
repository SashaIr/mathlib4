/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Algebra.DirectSum.LinearMap
public import Mathlib.RepresentationTheory.CharacterTheory.FDRepSimple

/-!
# Decomposition of a character into simple characters

Maschke's theorem says that a finite-dimensional representation of a finite group whose
order is invertible is a direct sum of simple ones.  Mathlib knows the theorem in the form
of the existence of complements, but does not deduce the decomposition of the character.
This file does it.

## Main definitions

* `FDRep.IsSimpleChar` : a function `G → k` which is the character of a simple object of
  `FDRep k G`.

## Main results

* `FDRep.trace_eq_add_trace_restrict` : the trace of an endomorphism preserving two
  complementary subspaces is the sum of the traces of its restrictions.
* `FDRep.exists_multiset_isSimpleChar` : the character of any object of `FDRep k G` is a
  sum of characters of simple objects.
-/

@[expose] public section

namespace FDRep

open CategoryTheory Representation LinearMap Module

universe u

variable {k G : Type u} [Field k] [Group G]

/-- The trace of an endomorphism which preserves two complementary subspaces is the sum of
the traces of its restrictions to them. -/
theorem trace_eq_add_trace_restrict {V : Type u} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (p q : Submodule k V) (h : IsCompl p q) (f : V →ₗ[k] V)
    (hp : Set.MapsTo f p p) (hq : Set.MapsTo f q q) :
    trace k V f = trace k p (f.restrict hp) + trace k q (f.restrict hq) := by
  classical
  set N : Bool → Submodule k V := fun b => if b then p else q with hN
  have hint : DirectSum.IsInternal N :=
    (DirectSum.isInternal_submodule_iff_isCompl N (i := true) (j := false) (by simp)
      (by ext b; cases b <;> simp)).2 (by simpa [hN] using h)
  have hf : ∀ b, Set.MapsTo f (N b) (N b) := by
    intro b; cases b <;> simpa [hN] using ‹_›
  rw [trace_eq_sum_trace_restrict hint hf, Fintype.sum_bool]
  rfl

/-- A function on `G` which is the character of a simple object of `FDRep k G`. -/
def IsSimpleChar (chi : G → k) : Prop :=
  ∃ V : FDRep k G, Simple V ∧ V.character = chi

variable [IsAlgClosed k] [Finite G] [NeZero (Nat.card G : k)]

/-- **Every character is a sum of simple characters**: the character of a
finite-dimensional representation of a finite group whose order is invertible in the
(algebraically closed) field `k` is the sum of the characters of the simple constituents
of the representation. -/
theorem exists_multiset_isSimpleChar (X : FDRep k G) :
    ∃ l : Multiset (G → k), (∀ c ∈ l, IsSimpleChar c) ∧ X.character = l.sum := by
  classical
  induction hn : finrank k X using Nat.strong_induction_on generalizing X with
  | _ n ih =>
    subst hn
    rcases Nat.eq_zero_or_pos (finrank k X) with h0 | hpos
    · refine ⟨0, by simp, ?_⟩
      have hsub : Subsingleton X := by
        rw [← finrank_zero_iff (R := k)]
        exact h0
      funext g
      have : X.ρ g = 0 := by ext v; exact Subsingleton.elim _ _
      simp [FDRep.character, this]
    · by_cases hs : Simple X
      · exact ⟨{X.character}, by simpa using ⟨X, hs, rfl⟩, by simp⟩
      obtain ⟨U, hUbot, hUtop⟩ := exists_subrepresentation_of_not_simple X hpos hs
      obtain ⟨U', hcompl⟩ := exists_isCompl U
      have hcompl' : IsCompl U.toSubmodule U'.toSubmodule := by
        constructor
        · rw [disjoint_iff, ← Subrepresentation.toSubmodule_inf]
          exact congrArg Subrepresentation.toSubmodule hcompl.disjoint.eq_bot
        · rw [codisjoint_iff, ← Subrepresentation.toSubmodule_sup]
          exact congrArg Subrepresentation.toSubmodule hcompl.codisjoint.eq_top
      have hrank : finrank k U.toSubmodule + finrank k U'.toSubmodule = finrank k X :=
        Submodule.finrank_add_eq_of_isCompl hcompl'
      have hUpos : 0 < finrank k U.toSubmodule := by
        rcases Nat.eq_zero_or_pos (finrank k U.toSubmodule) with h | h
        · exact absurd (Subrepresentation.toSubmodule_injective
            (show U.toSubmodule = (⊥ : Subrepresentation X.ρ).toSubmodule from
              Submodule.finrank_eq_zero.mp h)) hUbot
        · exact h
      have hU'pos : 0 < finrank k U'.toSubmodule := by
        rcases Nat.eq_zero_or_pos (finrank k U'.toSubmodule) with h | h
        · exfalso
          refine hUtop ?_
          have hUrank : finrank k U.toSubmodule = finrank k X := by omega
          have : U.toSubmodule = ⊤ := Submodule.eq_top_of_finrank_eq hUrank
          exact Subrepresentation.toSubmodule_injective (by
            change U.toSubmodule = (⊤ : Submodule k X.V)
            exact this)
        · exact h
      -- the two pieces, as objects of `FDRep k G`
      set A : FDRep k G := FDRep.of U.toRepresentation with hA
      set B : FDRep k G := FDRep.of U'.toRepresentation with hB
      have hchar : X.character = A.character + B.character := by
        funext g
        have hp : Set.MapsTo (X.ρ g) U.toSubmodule U.toSubmodule := fun v hv =>
          U.apply_mem_toSubmodule g hv
        have hq : Set.MapsTo (X.ρ g) U'.toSubmodule U'.toSubmodule := fun v hv =>
          U'.apply_mem_toSubmodule g hv
        exact trace_eq_add_trace_restrict _ _ hcompl' _ hp hq
      have hArank : finrank k A = finrank k U.toSubmodule := rfl
      have hBrank : finrank k B = finrank k U'.toSubmodule := rfl
      obtain ⟨la, hla, hlaeq⟩ := ih (finrank k A) (by omega) A rfl
      obtain ⟨lb, hlb, hlbeq⟩ := ih (finrank k B) (by omega) B rfl
      refine ⟨la + lb, ?_, ?_⟩
      · intro c hc
        rcases Multiset.mem_add.1 hc with h | h
        · exact hla c h
        · exact hlb c h
      · rw [hchar, hlaeq, hlbeq, Multiset.sum_add]

end FDRep
