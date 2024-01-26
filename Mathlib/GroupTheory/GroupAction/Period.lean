/-
Copyright (c) 2024 Emilie Burgun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emilie Burgun
-/

import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Dynamics.PeriodicPts
import Mathlib.GroupTheory.Exponent
import Mathlib.Data.Int.Lemmas

/-!
# Period of a group action

This module defines some helpful lemmas around [`MulAction.period`] and [`AddAction.period`].
The period of a point `a` by a group element `g` is the smallest `m` such that `g ^ m • a = a`
(resp. `(m • g) +ᵥ a = a`) for a given `g : G` and `a : α`.

If such an `m` does not exist,
then by convention `MulAction.period` and `AddAction.period` return 0.
-/

namespace MulAction

universe u v
variable {α : Type v}
variable {G : Type u} [Group G] [MulAction G α]
variable {M : Type u} [Monoid M] [MulAction M α]

theorem period_eq_zero_iff_forall_pow {m : M} {a : α} :
    period m a = 0 ↔ ∀ n > 0, m ^ n • a ≠ a := by
  simp_rw [period, ← smul_iterate, Function.minimalPeriod_eq_zero_iff_nmem_periodicPts,
    Function.mem_periodicPts, Function.IsPeriodicPt, Function.IsFixedPt, not_exists, not_and]

theorem period_eq_zero_iff_forall_zpow {g : G} {a : α} :
    period g a = 0 ↔ ∀ j : ℤ, j ≠ 0 → g ^ j • a ≠ a := by
  rw [period_eq_zero_iff_forall_pow]
  constructor
  · intro h₁ j j_ne_zero
    specialize h₁ j.natAbs (Int.natAbs_pos.mpr j_ne_zero)
    rw [← zpow_ofNat] at h₁
    cases Int.natAbs_eq j with
    | inl h₂ =>
      rwa [← h₂] at h₁
    | inr h₂ =>
      rw [← neg_eq_iff_eq_neg] at h₂
      rwa [← h₂, ne_eq, zpow_neg, smul_eq_iff_eq_inv_smul, inv_inv, eq_comm] at h₁
  · intro h n n_pos
    specialize h n (Int.coe_nat_ne_zero_iff_pos.mpr n_pos)
    rwa [zpow_ofNat] at h

/-- If the action is periodic, then a lower bound for its period can be computed. -/
@[to_additive]
theorem le_period_of_moved {m : M} {a : α} {n : ℕ} (period_pos : 0 < period m a)
    (moved : ∀ k, 0 < k → k < n → m^k • a ≠ a) : n ≤ period m a := by
  by_contra period_le_n
  rw [not_le] at period_le_n
  apply moved _ period_pos period_le_n
  exact smul_pow_period_fixed m a

/-- If for some `n`, `m ^ n • a = a`, then `period m a ≤ n`. -/
@[to_additive]
theorem period_le_of_fixed {m : M} {a : α} {n : ℕ} (n_pos : 0 < n) (fixed : m ^ n • a = a) :
    period m a ≤ n := by
  rw [period_eq_minimalPeriod]
  rw [fixed_iff_isPeriodicPt] at fixed
  exact Function.IsPeriodicPt.minimalPeriod_le n_pos fixed

theorem period_le_natAbs_of_fixed {g : G} {a : α} {j : ℤ} (j_ne_zero : j ≠ 0)
    (fixed : g ^ j • a = a) : period g a ≤ j.natAbs := by
  apply period_le_of_fixed (Int.natAbs_pos.mpr j_ne_zero)
  cases Int.natAbs_eq j with
  | inl h_eq =>
    rwa [← zpow_ofNat, ← h_eq]
  | inr h_eq =>
    rw [← neg_eq_iff_eq_neg] at h_eq
    rwa [← zpow_ofNat, ← h_eq, zpow_neg, smul_eq_iff_eq_inv_smul, inv_inv, eq_comm]

/-- If for some `n`, `m ^ n • a = a`, then `0 < period m a`. -/
@[to_additive]
theorem period_pos_of_fixed {m : M} {a : α} {n : ℕ} (n_pos : 0 < n) (fixed : m ^ n • a = a) :
    0 < period m a := by
  rw [fixed_iff_isPeriodicPt] at fixed
  rw [period_eq_minimalPeriod]
  exact Function.IsPeriodicPt.minimalPeriod_pos n_pos fixed

@[to_additive]
theorem period_eq_one_of_fixed {m : M} {a : α} (fixed : m • a = a) : period m a = 1 := by
  symm
  rw [← pow_one m] at fixed
  refine Nat.eq_of_le_of_lt_succ (period_le_of_fixed Nat.one_pos fixed) ?pos
  rw [Nat.lt_add_left_iff_pos]
  exact period_pos_of_fixed Nat.one_pos fixed

/-- For any non-zero `n` less than the period, `a` is moved by `m^n`. -/
@[to_additive]
theorem moved_of_lt_period {m : M} {a : α} {n : ℕ} (n_pos : 0 < n) (n_lt_period : n < period m a) :
    m^n • a ≠ a := by
  intro a_fixed
  apply Nat.not_le.mpr n_lt_period
  exact period_le_of_fixed n_pos a_fixed

/-!
If `g ^ i • x = g ^ j • x` (resp. `(i • g) +ᵥ x = (j • g) +ᵥ x`), then `period g x` divides `i - j`.
If the action of `g` on `x` is aperiodic, then this is equivalent to say that `i = j`.
-/

@[to_additive]
theorem smul_zpow_eq_of_period_dvd {g : G} {x : α} {i j : ℤ} :
    g ^ i • x = g ^ j • x ↔ (period g x : ℤ) ∣ i - j := by
  rw [eq_comm, smul_eq_iff_eq_inv_smul, eq_comm, ← mul_smul, ← zpow_neg, ← zpow_add, add_comm,
    ← sub_eq_add_neg, zpow_smul_eq_iff_period_dvd]

@[to_additive]
theorem smul_pow_eq_of_period_dvd {g : G} {x : α} {n m : ℕ} :
    g ^ n • x = g ^ m • x ↔ period g x ∣ Int.natAbs (↑n - ↑m) := by
  rw [← zpow_ofNat, ← zpow_ofNat, smul_zpow_eq_of_period_dvd, ← dvd_abs, ← Int.coe_natAbs,
    Int.ofNat_dvd]

section MonoidExponent

/-! ## `MulAction.period` and group exponents

The period of a given element `m : M` can be bounded by the `Monoid.exponent M` or `orderOf m`.
-/

@[to_additive]
theorem period_pos_of_orderOf_pos {m : M} (order_pos : 0 < orderOf m) (a : α):
    0 < period m a := by
  apply period_pos_of_fixed order_pos
  rw [pow_orderOf_eq_one, one_smul]

@[to_additive]
theorem period_le_orderOf {m : M} (order_pos : 0 < orderOf m) (a : α):
    period m a ≤ orderOf m := by
  apply period_le_of_fixed order_pos
  rw [pow_orderOf_eq_one, one_smul]

@[to_additive]
theorem period_pos_of_exponent_pos (exp_pos : 0 < Monoid.exponent M) (m : M) (a : α) :
    0 < period m a := by
  apply period_pos_of_fixed exp_pos
  rw [Monoid.pow_exponent_eq_one, one_smul]

@[to_additive]
theorem period_le_exponent (exp_pos : 0 < Monoid.exponent M) (m : M) (a : α) :
    period m a ≤ Monoid.exponent M := by
  apply period_le_of_fixed exp_pos
  rw [Monoid.pow_exponent_eq_one, one_smul]

variable (α)

@[to_additive]
theorem period_bounded_of_exponent_pos (exp_pos : 0 < Monoid.exponent M) (m : M) :
    BddAbove (Set.range (fun a : α => period m a)) := by
  use Monoid.exponent M
  simp [upperBounds]
  apply period_le_exponent exp_pos

end MonoidExponent

section InjOn

/-! ## Injectivity of the action in relation to `period`
-/

/--
All the values `g ^ i` with `i < period g x` will map `x` to different points.
-/
@[to_additive "All the values `i • g` with `i < period g x` will map `x` to different points."]
theorem smul_injOn_pow_lt_period (g : G) (x : α) :
    { g ^ i | i < period g x }.InjOn (· • x) := by
  intro h ⟨a, a_lt_n, ga_eq_h⟩ i ⟨b, b_lt_n, gb_eq_i⟩ img_eq
  rw [← ga_eq_h, ← gb_eq_i, MulAction.smul_pow_eq_of_period_dvd] at img_eq
  rw [← ga_eq_h, ← gb_eq_i]
  by_cases eq : a = b
  · rw [eq]
  · exfalso
    refine Nat.not_lt.mpr
      (Nat.le_of_dvd ?pos img_eq)
      (Int.natAbs_coe_sub_coe_lt_of_lt b_lt_n a_lt_n)
    rwa [Int.natAbs_sub_pos_iff, ne_eq, Nat.cast_inj]

/--
If the action of `g` on `x` is aperiodic, then the action of `g ^ i` on `x` is injective.
-/
@[to_additive
  "If the action of `g` on `x` is aperiodic, then the action of `i • g` on `x` is injective."]
theorem smul_injOn_zpow_of_period_eq_zero {g : G} {x : α} (period_eq_zero : period g x = 0) :
    { g ^ i | i : ℤ }.InjOn (· • x) := by
  intro g₁ ⟨i, g₁_eq⟩ g₂ ⟨j, g₂_eq⟩ img_eq
  rw [← g₁_eq, ← g₂_eq, MulAction.smul_zpow_eq_of_period_dvd, period_eq_zero,
    Int.ofNat_zero, zero_dvd_iff, sub_eq_zero] at img_eq
  rw [← g₁_eq, ← g₂_eq, img_eq]

end InjOn

end MulAction
