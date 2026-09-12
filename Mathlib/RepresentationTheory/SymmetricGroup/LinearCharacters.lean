/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.GroupTheory.Perm.Sign

/-!
# The linear characters of the symmetric group

Following `theories/SymGroup/reprSn.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we classify the one dimensional
representations of the symmetric group, that is its linear characters: the trivial one
and the signature (Coq `repr1`).  A one dimensional representation is the same thing as a
morphism from the symmetric group to the invertible scalars, so the statements below are
about morphisms from `Equiv.Perm α` to a commutative group.

The key point is that all the transpositions are conjugate, hence have the same image
under such a morphism, so that the image of a permutation only depends on the parity of
the number of transpositions needed to write it, that is on its signature.

## Main definitions and results

* `Equiv.Perm.map_swap_eq_map_swap` : all the transpositions have the same image.
* `Equiv.Perm.map_eq_one_of_sign_eq_one` : an even permutation is in the kernel, so that a
  morphism to a commutative group kills the alternating group.
* `Equiv.Perm.map_eq_map_of_sign_eq` : the image of a permutation only depends on its
  signature.
* `Equiv.Perm.signChar` : the signature as a morphism to the invertible elements of a ring.
* `Equiv.Perm.eq_one_or_eq_signChar` : a morphism from the symmetric group to the invertible
  elements of an integral domain is either trivial or the signature (Coq `repr1`).
-/

@[expose] public section

open Equiv

namespace Equiv.Perm


variable {α : Type*} [DecidableEq α] [Fintype α] {G : Type*} [CommGroup G]

omit [Fintype α] in
/-- All the transpositions have the same image under a morphism to a commutative group,
because they are all conjugate. -/
theorem map_swap_eq_map_swap (f : Perm α →* G) {a b x y : α} (hab : a ≠ b) (hxy : x ≠ y) :
    f (swap a b) = f (swap x y) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 (Equiv.Perm.isConj_swap hab hxy)
  rw [← hc, map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]

omit [Fintype α] in
/-- The image of a transposition squares to one. -/
theorem map_swap_sq (f : Perm α →* G) {a b : α} : f (swap a b) * f (swap a b) = 1 := by
  rw [← map_mul, Equiv.swap_mul_self, map_one]

/-- Auxiliary induction: an even permutation is in the kernel of a morphism to a
commutative group, and an odd one has the image of the transpositions. -/
theorem map_eq_one_and_map_eq_map_swap (f : Perm α →* G) (σ : Perm α) :
    (sign σ = 1 → f σ = 1) ∧
      (∀ a b : α, a ≠ b → sign σ = -1 → f σ = f (swap a b)) := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one =>
    exact ⟨fun _ => map_one f, fun a b _ h => by rw [map_one] at h; exact absurd h (by decide)⟩
  | swap_mul τ x y hxy ih =>
    have hsign : sign (swap x y * τ) = -sign τ := by
      rw [map_mul, Equiv.Perm.sign_swap hxy, neg_one_mul]
    refine ⟨fun h => ?_, fun a b hab h => ?_⟩
    · have hτ : sign τ = -1 := by
        rw [hsign] at h
        exact neg_eq_iff_eq_neg.1 h
      rw [map_mul, ih.2 x y hxy hτ]
      exact map_swap_sq f
    · have hτ : sign τ = 1 := by
        rw [hsign] at h
        exact neg_inj.1 h
      rw [map_mul, ih.1 hτ, mul_one]
      exact map_swap_eq_map_swap f hxy hab

/-- A morphism from the symmetric group to a commutative group kills the even
permutations. -/
theorem map_eq_one_of_sign_eq_one (f : Perm α →* G) {σ : Perm α} (h : sign σ = 1) :
    f σ = 1 := (map_eq_one_and_map_eq_map_swap f σ).1 h

/-- Under a morphism to a commutative group, the image of a permutation only depends on
its signature. -/
theorem map_eq_map_of_sign_eq (f : Perm α →* G) {σ τ : Perm α} (h : sign σ = sign τ) :
    f σ = f τ := by
  have hker : f (σ * τ⁻¹) = 1 := by
    refine map_eq_one_of_sign_eq_one f ?_
    rw [map_mul, map_inv, h]
    exact mul_inv_cancel _
  rw [map_mul, map_inv, ← div_eq_mul_inv] at hker
  exact eq_of_div_eq_one hker

/-- The signature as a morphism to the invertible elements of a ring `K`, that is the sign
representation of the symmetric group over `K` (Coq `sign_repr`). -/
def signChar (α : Type*) [DecidableEq α] [Fintype α] (K : Type*) [Ring K] : Perm α →* Kˣ :=
  (Units.map (Int.castRingHom K).toMonoidHom).comp (Equiv.Perm.sign (α := α))

@[simp] lemma signChar_apply {K : Type*} [Ring K] (σ : Perm α) :
    ((signChar α K σ : Kˣ) : K) = (sign σ : ℤ) := rfl

variable {K : Type*} [CommRing K] [IsDomain K]

/-- **The linear characters of the symmetric group**: a morphism from the symmetric group
to the invertible elements of an integral domain is either trivial or the signature
(Coq `repr1`). -/
theorem eq_one_or_eq_signChar (f : Perm α →* Kˣ) : f = 1 ∨ f = signChar α K := by
  by_cases hcard : ∃ a b : α, a ≠ b
  · obtain ⟨a, b, hab⟩ := hcard
    have hz : (f (swap a b) : K) * (f (swap a b) : K) = 1 := by
      simpa using congrArg (Units.val) (map_swap_sq f (a := a) (b := b))
    have hz' : (f (swap a b) : K) = 1 ∨ (f (swap a b) : K) = -1 := by
      rcases mul_self_eq_one_iff.1 hz with h | h
      · exact Or.inl h
      · exact Or.inr h
    have hodd : ∀ σ : Perm α, sign σ = -1 → f σ = f (swap a b) := fun σ h =>
      (map_eq_one_and_map_eq_map_swap f σ).2 a b hab h
    have heven : ∀ σ : Perm α, sign σ = 1 → f σ = 1 := fun σ h =>
      map_eq_one_of_sign_eq_one f h
    rcases hz' with h1 | h1
    · refine Or.inl (MonoidHom.ext fun σ => ?_)
      rcases Int.units_eq_one_or (sign σ) with h | h
      · rw [heven σ h, MonoidHom.one_apply]
      · rw [hodd σ h, MonoidHom.one_apply]
        exact Units.ext h1
    · refine Or.inr (MonoidHom.ext fun σ => ?_)
      refine Units.ext ?_
      rcases Int.units_eq_one_or (sign σ) with h | h
      · rw [heven σ h, signChar_apply, h]
        simp
      · rw [hodd σ h, signChar_apply, h, h1]
        simp
  · push Not at hcard
    have hsub : Subsingleton α := ⟨fun a b => hcard a b⟩
    refine Or.inl (MonoidHom.ext fun σ => ?_)
    have : σ = 1 := Subsingleton.elim _ _
    rw [this, map_one, MonoidHom.one_apply]

end Equiv.Perm
