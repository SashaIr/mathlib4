/-
Copyright (c) 2026 Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/
import Mathlib.RepresentationTheory.CharacterTheory.VirtualCharacter

/-!
# Permutation representations and their characters

The representation of a group `G` on the functions from a finite `G`-set `X` to a field
`k`, and the fact that its character counts the fixed points of the action.  When `X` is
the set of cosets of a subgroup `H`, summing a class function against that character
amounts to summing it over `H`; this is the shape in which the character of a
representation induced from the trivial character of `H` will be computed.

## Main definitions

* `FDRep.permRep k G X` : the permutation representation of `G` on `X → k`.

## Main results

* `FDRep.character_permRep` : the character of `permRep k G X` at `g` is the number of
  fixed points of `g` on `X`.
* `FDRep.sum_card_fixedPoints_quotient_mul` : for a class function `F` on `G`,
  `∑_σ #Fix_{G/H}(σ) · F σ = [G : H] · ∑_{h ∈ H} F h`.
-/

namespace FDRep

open CategoryTheory Representation LinearMap Module

universe u

variable (k : Type u) [Field k] (G X : Type u) [Group G] [Finite X] [MulAction G X]

/-- The permutation representation of `G` on the functions from a `G`-set `X` to `k`. -/
def permRep : Representation k G (X → k) where
  toFun g := LinearMap.funLeft k k (fun x => g⁻¹ • x)
  map_one' := by ext f x; simp [LinearMap.funLeft]
  map_mul' g h := by ext f x; simp [LinearMap.funLeft, mul_smul]

instance : Module.Finite k (X → k) := by
  have : Fintype X := Fintype.ofFinite X
  infer_instance

variable {G X}

/-- **The character of a permutation representation counts fixed points.** -/
theorem character_permRep (g : G) :
    (FDRep.of (permRep k G X)).character g = (Nat.card {x : X // g • x = x} : k) := by
  classical
  have : Fintype X := Fintype.ofFinite X
  have h1 : (FDRep.of (permRep k G X)).character g = trace k (X → k) (permRep k G X g) := rfl
  rw [h1, LinearMap.trace_eq_matrix_trace k (Pi.basisFun k X), Matrix.trace]
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr]
  have hx : ∀ x : X, ((permRep k G X) g) (Pi.single x 1) x = if g • x = x then (1 : k) else 0 := by
    intro x
    have hval : ((permRep k G X) g) (Pi.single x 1) x
        = (Pi.single x (1 : k) : X → k) (g⁻¹ • x) := by
      simp [permRep]
    have hiff : (g⁻¹ • x = x) ↔ (g • x = x) := by
      rw [inv_smul_eq_iff]
      exact eq_comm
    rw [hval, Pi.single_apply]
    exact if_congr hiff rfl rfl
  rw [Finset.sum_congr rfl fun x _ => hx x, Finset.sum_boole, Nat.card_eq_fintype_card,
    Fintype.card_subtype]

/-- The character of a permutation representation is a virtual character. -/
theorem isVirtualChar_card_fixedPoints [IsAlgClosed k] [Finite G] [NeZero (Nat.card G : k)] :
    IsVirtualChar (fun g : G => (Nat.card {x : X // g • x = x} : k)) := by
  have h := IsVirtualChar.of_character (FDRep.of (permRep k G X))
  have heq : (FDRep.of (permRep k G X)).character
      = fun g : G => (Nat.card {x : X // g • x = x} : k) :=
    funext fun g => character_permRep k (X := X) g
  rwa [heq] at h

/-! ### Summing a class function against a coset permutation character -/

variable {k}

/-- For a class function `F` on a finite group `G` and a subgroup `H`, summing `F` against
the permutation character of the action of `G` on the cosets of `H` amounts to summing `F`
over `H`, up to the index of `H`. -/
theorem sum_card_fixedPoints_quotient_mul {R : Type*} [CommRing R] [Fintype G] (H : Subgroup G)
    [Fintype H] (F : G → R) (hF : ∀ a b : G, F (b⁻¹ * a * b) = F a) :
    ∑ sigma : G, (Nat.card {q : G ⧸ H // sigma • q = q} : R) * F sigma
      = (Nat.card (G ⧸ H) : R) * ∑ h : H, F h := by
  classical
  have : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hcount : ∀ sigma : G, (Nat.card {q : G ⧸ H // sigma • q = q} : R)
      = ∑ q : G ⧸ H, if sigma • q = q then (1 : R) else 0 := by
    intro sigma
    rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hswap : ∑ sigma : G, (Nat.card {q : G ⧸ H // sigma • q = q} : R) * F sigma
      = ∑ q : G ⧸ H, ∑ sigma : G, if sigma • q = q then F sigma else 0 := by
    have h1 : ∀ sigma : G, (Nat.card {q : G ⧸ H // sigma • q = q} : R) * F sigma
        = ∑ q : G ⧸ H, if sigma • q = q then F sigma else 0 := by
      intro sigma
      rw [hcount sigma, Finset.sum_mul]
      exact Finset.sum_congr rfl fun q _ => by by_cases h : sigma • q = q <;> simp [h]
    rw [Finset.sum_congr rfl fun sigma _ => h1 sigma]
    exact Finset.sum_comm
  have hq : ∀ q : G ⧸ H, (∑ sigma : G, if sigma • q = q then F sigma else 0) = ∑ h : H, F h := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have hconj : ∑ sigma : G, (if sigma • (g : G ⧸ H) = (g : G ⧸ H) then F sigma else 0)
        = ∑ tau : G, (if (g * tau * g⁻¹) • (g : G ⧸ H) = (g : G ⧸ H)
            then F (g * tau * g⁻¹) else 0) :=
      (Fintype.sum_equiv (MulAut.conj g).toEquiv _ _ fun tau => rfl).symm
    rw [hconj]
    have hterm : ∀ tau : G, (if (g * tau * g⁻¹) • (g : G ⧸ H) = (g : G ⧸ H)
        then F (g * tau * g⁻¹) else 0) = if tau ∈ H then F tau else 0 := by
      intro tau
      have hmem : ((g * tau * g⁻¹) • (g : G ⧸ H) = (g : G ⧸ H)) ↔ tau ∈ H := by
        rw [show (g * tau * g⁻¹) • (g : G ⧸ H) = ((g * tau * g⁻¹ * g : G) : G ⧸ H) from rfl,
          QuotientGroup.eq]
        constructor
        · intro h
          simpa [mul_assoc] using h
        · intro h
          simpa [mul_assoc] using h
      have hval : F (g * tau * g⁻¹) = F tau := by
        have := hF tau g⁻¹
        simpa using this
      rw [hval]
      exact if_congr hmem rfl rfl
    rw [Finset.sum_congr rfl fun tau _ => hterm tau, ← Finset.sum_filter]
    exact Finset.sum_subtype _ (fun x => by simp) F
  rw [hswap, Finset.sum_congr rfl fun q _ => hq q, Finset.sum_const, Nat.card_eq_fintype_card,
    nsmul_eq_mul, Finset.card_univ]

end FDRep
