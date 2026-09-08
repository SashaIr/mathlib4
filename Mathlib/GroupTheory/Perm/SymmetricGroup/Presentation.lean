/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.SymmetricGroup.SwapRelations

/-!
# The Coxeter presentation of the symmetric group

Following `theories/SymGroup/presentSn.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we prove that the symmetric group
`Equiv.Perm (Fin (n + 1))` is the Coxeter group of type `Aₙ`: the adjacent transpositions
`(i, i+1)` generate it, and the only relations between them are the Coxeter relations
`s_i² = 1`, `(s_i s_{i+1})³ = 1` and `(s_i s_j)² = 1` for `|i - j| ≥ 2`.

The surjectivity of the resulting morphism from the abstract Coxeter group is the fact
that the adjacent transpositions generate the symmetric group.  Injectivity is proved by
induction on `n`: writing `N = n + 1`, every element of the Coxeter group of type `A_N`
can be written as `v · t_i` where `v` lies in the image of the Coxeter group of type
`A_{N-1}` and `t_i = s_{N-1} s_{N-2} ⋯ s_{N-i}` (`Equiv.Perm.cosetRep`), and the image of `t_i`
in the symmetric group moves the last point as soon as `i ≠ 0`.

## Main definitions and results

* `Equiv.Perm.adjSwap` : the adjacent transposition `(i, i+1)` of `Fin (n + 1)`.
* `Equiv.Perm.permOfCox` : the morphism from the Coxeter group of type `Aₙ` to
  `Equiv.Perm (Fin (n + 1))`.
* `Equiv.Perm.permOfCox_bijective` : it is an isomorphism.
* `Equiv.Perm.permCoxeterSystem` : the resulting Coxeter system of type `Aₙ` on
  `Equiv.Perm (Fin (n + 1))`, whose simple reflections are the adjacent transpositions.
-/

open Equiv CoxeterMatrix

namespace Equiv.Perm


/-! ### The morphism to the symmetric group -/

/-- The adjacent transposition `(i, i+1)` of `Fin (n + 1)`. -/
def adjSwap (n : ℕ) (i : Fin n) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.swap i.castSucc i.succ

/-- The adjacent transpositions satisfy the Coxeter relations of type `Aₙ`. -/
lemma isLiftable_adjSwap (n : ℕ) : (CoxeterMatrix.Aₙ n).IsLiftable (adjSwap n) := by
  intro i j
  have hcs : ∀ a : Fin n, ((a.castSucc : Fin (n + 1)) : ℕ) = (a : ℕ) := fun _ => rfl
  have hsc : ∀ a : Fin n, ((a.succ : Fin (n + 1)) : ℕ) = (a : ℕ) + 1 := fun _ => rfl
  by_cases hij : i = j
  · subst hij
    have hM : (CoxeterMatrix.Aₙ n) i i = 1 := by
      simp only [CoxeterMatrix.Aₙ, Matrix.of_apply, ite_eq_left]
    rw [hM, pow_one, adjSwap, Equiv.swap_mul_self]
  · have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    by_cases hadj : (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j
    · have hM : (CoxeterMatrix.Aₙ n) i j = 3 := by
        simp only [CoxeterMatrix.Aₙ, Matrix.of_apply, ite_eq_right hij, ite_eq_left hadj]
      rw [hM, adjSwap, adjSwap]
      rcases hadj with h | h
      · have he : (j.succ : Fin (n + 1)) = i.castSucc := Fin.ext (by rw [hsc, hcs]; omega)
        have h1 : (i.succ : Fin (n + 1)) ≠ j.succ := Fin.ne_of_val_ne (by rw [hsc, hsc]; omega)
        have h2 : (j.succ : Fin (n + 1)) ≠ j.castSucc := Fin.ne_of_val_ne (by rw [hsc, hcs]; omega)
        have h3 : (i.succ : Fin (n + 1)) ≠ j.castSucc := Fin.ne_of_val_ne (by rw [hsc, hcs]; omega)
        rw [← he, Equiv.swap_comm j.succ i.succ, Equiv.swap_comm j.castSucc j.succ]
        exact swap_mul_swap_pow_three h1 h2 h3
      · have he : (i.succ : Fin (n + 1)) = j.castSucc := Fin.ext (by rw [hsc, hcs]; omega)
        have h1 : (i.castSucc : Fin (n + 1)) ≠ i.succ := Fin.ne_of_val_ne (by rw [hcs, hsc]; omega)
        have h2 : (i.succ : Fin (n + 1)) ≠ j.succ := Fin.ne_of_val_ne (by rw [hsc, hsc]; omega)
        have h3 : (i.castSucc : Fin (n + 1)) ≠ j.succ := Fin.ne_of_val_ne (by rw [hcs, hsc]; omega)
        rw [← he]
        exact swap_mul_swap_pow_three h1 h2 h3
    · have hM : (CoxeterMatrix.Aₙ n) i j = 2 := by
        simp only [CoxeterMatrix.Aₙ, Matrix.of_apply, ite_eq_right hij, ite_eq_right hadj]
      push Not at hadj
      obtain ⟨h1, h2⟩ := hadj
      rw [hM, adjSwap, adjSwap]
      exact swap_mul_swap_pow_two (Fin.ne_of_val_ne (by rw [hcs, hcs]; omega))
        (Fin.ne_of_val_ne (by rw [hcs, hsc]; omega))
        (Fin.ne_of_val_ne (by rw [hsc, hcs]; omega))
        (Fin.ne_of_val_ne (by rw [hsc, hsc]; omega))

/-- The morphism from the Coxeter group of type `Aₙ` to the symmetric group of
`Fin (n + 1)`, sending the `i`-th simple reflection to the transposition `(i, i+1)`. -/
noncomputable def permOfCox (n : ℕ) : (CoxeterMatrix.Aₙ n).Group →* Equiv.Perm (Fin (n + 1)) :=
  (CoxeterMatrix.Aₙ n).toCoxeterSystem.lift ⟨adjSwap n, isLiftable_adjSwap n⟩

@[simp] lemma permOfCox_simple (n : ℕ) (i : Fin n) :
    permOfCox n ((CoxeterMatrix.Aₙ n).simple i) = adjSwap n i :=
  (CoxeterMatrix.Aₙ n).toCoxeterSystem.lift_apply_simple (isLiftable_adjSwap n) i

/-- The adjacent transpositions generate the symmetric group, so `permOfCox` is
surjective. -/
theorem permOfCox_surjective (n : ℕ) : Function.Surjective (permOfCox n) := by
  intro sigma
  have hmem : sigma ∈ Submonoid.closure
      (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]
    exact Submonoid.mem_top sigma
  induction hmem using Submonoid.closure_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact ⟨(CoxeterMatrix.Aₙ n).simple i, permOfCox_simple n i⟩
  | one => exact ⟨1, map_one _⟩
  | mul x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a * b, map_mul _ _ _⟩

/-! ### Generators indexed by natural numbers -/

/-- The `k`-th simple reflection of the Coxeter group of type `A_N`, with the convention
that it is the identity when `k` is out of range. -/
noncomputable def coxGen (N k : ℕ) : (CoxeterMatrix.Aₙ N).Group :=
  if h : k < N then (CoxeterMatrix.Aₙ N).simple ⟨k, h⟩ else 1

lemma coxGen_of_lt {N k : ℕ} (h : k < N) :
    coxGen N k = (CoxeterMatrix.Aₙ N).simple ⟨k, h⟩ := dite_eq_left h

lemma coxGen_of_le {N k : ℕ} (h : N ≤ k) : coxGen N k = 1 := dite_eq_right (by omega)

/-- In a group, two involutions whose product is an involution commute. -/
lemma mul_comm_of_sq {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (h : (a * b) ^ 2 = 1) : a * b = b * a := by
  have hinv : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact h)
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hb, inv_eq_of_mul_eq_one_right ha] at hinv
  exact hinv.symm

/-- In a group, two involutions whose product has order dividing three satisfy the braid
relation. -/
lemma braid_of_cube {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (h : (a * b) ^ 3 = 1) : a * b * a = b * a * b := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h3 : (a * b * a) * (b * a * b) = 1 := by
    rw [← h]; simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have hX : (a * b * a)⁻¹ = b * a * b := inv_eq_of_mul_eq_one_right h3
  rw [mul_inv_rev, mul_inv_rev, hai, hbi] at hX
  rw [← hX]
  simp only [mul_assoc]

@[simp] lemma coxGen_mul_self (N k : ℕ) : coxGen N k * coxGen N k = 1 := by
  rw [coxGen]
  split_ifs with h
  · exact (CoxeterMatrix.Aₙ N).toCoxeterSystem.simple_mul_simple_self _
  · exact mul_one 1

lemma coxGen_comm {N k l : ℕ} (h : k + 1 < l) :
    coxGen N k * coxGen N l = coxGen N l * coxGen N k := by
  by_cases hl : l < N
  · have hk : k < N := by omega
    have hM : (CoxeterMatrix.Aₙ N) ⟨k, hk⟩ ⟨l, hl⟩ = 2 := by
      simp only [CoxeterMatrix.Aₙ, Matrix.of_apply]
      rw [ite_eq_right (by simp only [Fin.mk.injEq]; omega), ite_eq_right (by omega)]
    have hpow := (CoxeterMatrix.Aₙ N).toCoxeterSystem.simple_mul_simple_pow ⟨k, hk⟩ ⟨l, hl⟩
    rw [hM] at hpow
    rw [coxGen_of_lt hk, coxGen_of_lt hl]
    exact mul_comm_of_sq ((CoxeterMatrix.Aₙ N).toCoxeterSystem.simple_mul_simple_self _)
      ((CoxeterMatrix.Aₙ N).toCoxeterSystem.simple_mul_simple_self _) hpow
  · rw [coxGen_of_le (by omega : N ≤ l), mul_one, one_mul]

lemma coxGen_braid {N k : ℕ} (h : k + 1 < N) :
    coxGen N k * coxGen N (k + 1) * coxGen N k
      = coxGen N (k + 1) * coxGen N k * coxGen N (k + 1) := by
  have hk : k < N := by omega
  have hM : (CoxeterMatrix.Aₙ N) ⟨k, hk⟩ ⟨k + 1, h⟩ = 3 := by
    simp only [CoxeterMatrix.Aₙ, Matrix.of_apply]
    rw [ite_eq_right (by simp only [Fin.mk.injEq]; omega), ite_eq_left (Or.inr trivial)]
  have hpow := (CoxeterMatrix.Aₙ N).toCoxeterSystem.simple_mul_simple_pow ⟨k, hk⟩ ⟨k + 1, h⟩
  rw [hM] at hpow
  rw [coxGen_of_lt hk, coxGen_of_lt h]
  exact braid_of_cube ((CoxeterMatrix.Aₙ N).toCoxeterSystem.simple_mul_simple_self _)
    ((CoxeterMatrix.Aₙ N).toCoxeterSystem.simple_mul_simple_self _) hpow

lemma permOfCox_coxGen {N k : ℕ} (h : k < N) :
    permOfCox N (coxGen N k) = adjSwap N ⟨k, h⟩ := by
  rw [coxGen_of_lt h, permOfCox_simple]

/-! ### The coset representatives -/

/-- The coset representative `t_i = s_{N-1} s_{N-2} ⋯ s_{N-i}`. -/
noncomputable def cosetRep (N : ℕ) : ℕ → (CoxeterMatrix.Aₙ N).Group
  | 0 => 1
  | (i + 1) => cosetRep N i * coxGen N (N - 1 - i)

@[simp] lemma cosetRep_zero (N : ℕ) : cosetRep N 0 = 1 := rfl

lemma cosetRep_succ (N i : ℕ) :
    cosetRep N (i + 1) = cosetRep N i * coxGen N (N - 1 - i) := rfl

lemma cosetRep_pred {N i : ℕ} (h : 0 < i) :
    cosetRep N i = cosetRep N (i - 1) * coxGen N (N - i) := by
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  rw [cosetRep_succ]
  congr 2
  omega

/-- A generator whose index is at distance at least two from all the indices occurring in
`t_i` commutes with `t_i`. -/
lemma coxGen_mul_cosetRep_comm {N : ℕ} : ∀ (i k : ℕ), k + 1 < N - i →
    coxGen N k * cosetRep N i = cosetRep N i * coxGen N k := by
  intro i
  induction i with
  | zero => intro k _; rw [cosetRep_zero, mul_one, one_mul]
  | succ i IH =>
      intro k h
      rw [cosetRep_succ, ← mul_assoc, IH k (by omega), mul_assoc, mul_assoc,
        coxGen_comm (show k + 1 < N - 1 - i by omega)]

/-- Multiplying `t_i` on the right by a generator of index larger than `N - i` amounts to
multiplying it on the left by the previous generator. -/
lemma cosetRep_mul_coxGen_of_lt {N : ℕ} : ∀ (i j : ℕ), i ≤ N → N - i < j → j < N →
    cosetRep N i * coxGen N j = coxGen N (j - 1) * cosetRep N i := by
  intro i
  induction i with
  | zero => intro j _ h1 h2; omega
  | succ i IH =>
      intro j hi h1 h2
      have hb : N - 1 - i + 1 = N - i := by omega
      by_cases hj : j = N - 1 - i + 1
      · have hipos : 0 < i := by omega
        subst hj
        rw [cosetRep_succ, cosetRep_pred hipos, hb]
        calc cosetRep N (i - 1) * coxGen N (N - i) * coxGen N (N - 1 - i) * coxGen N (N - i)
            = cosetRep N (i - 1) * (coxGen N (N - 1 - i + 1) * coxGen N (N - 1 - i)
                * coxGen N (N - 1 - i + 1)) := by rw [hb, mul_assoc, mul_assoc, mul_assoc]
          _ = cosetRep N (i - 1) * (coxGen N (N - 1 - i) * coxGen N (N - 1 - i + 1)
                * coxGen N (N - 1 - i)) := by
              rw [← coxGen_braid (show N - 1 - i + 1 < N by omega)]
          _ = (cosetRep N (i - 1) * coxGen N (N - 1 - i)) * coxGen N (N - 1 - i + 1)
                * coxGen N (N - 1 - i) := by rw [mul_assoc, mul_assoc, mul_assoc]
          _ = (coxGen N (N - 1 - i) * cosetRep N (i - 1)) * coxGen N (N - 1 - i + 1)
                * coxGen N (N - 1 - i) := by
              rw [← coxGen_mul_cosetRep_comm (i - 1) (N - 1 - i) (by omega)]
          _ = coxGen N (N - i - 1) * (cosetRep N (i - 1) * coxGen N (N - i)
                * coxGen N (N - 1 - i)) := by
              rw [show N - i - 1 = N - 1 - i by omega, hb, mul_assoc, mul_assoc, mul_assoc]
      · have hgt : N - 1 - i + 1 < j := by omega
        rw [cosetRep_succ, mul_assoc, coxGen_comm hgt, ← mul_assoc,
          IH j (by omega) (by omega) h2, mul_assoc]

/-! ### The embedding of the smaller Coxeter group -/

lemma Aₙ_castSucc (n : ℕ) (i j : Fin n) :
    (CoxeterMatrix.Aₙ (n + 1)) i.castSucc j.castSucc = (CoxeterMatrix.Aₙ n) i j := by
  simp only [CoxeterMatrix.Aₙ, Matrix.of_apply, Fin.castSucc_inj, Fin.val_castSucc]

/-- The morphism from the Coxeter group of type `A_n` to the Coxeter group of type
`A_{n+1}` sending the `i`-th simple reflection to the `i`-th simple reflection. -/
noncomputable def coxEmbed (n : ℕ) :
    (CoxeterMatrix.Aₙ n).Group →* (CoxeterMatrix.Aₙ (n + 1)).Group :=
  (CoxeterMatrix.Aₙ n).toCoxeterSystem.lift
    ⟨fun i => (CoxeterMatrix.Aₙ (n + 1)).simple i.castSucc, by
      intro i j
      rw [← Aₙ_castSucc n i j]
      exact (CoxeterMatrix.Aₙ (n + 1)).toCoxeterSystem.simple_mul_simple_pow _ _⟩

@[simp] lemma coxEmbed_simple (n : ℕ) (i : Fin n) :
    coxEmbed n ((CoxeterMatrix.Aₙ n).simple i)
      = (CoxeterMatrix.Aₙ (n + 1)).simple i.castSucc :=
  (CoxeterMatrix.Aₙ n).toCoxeterSystem.lift_apply_simple _ i

lemma coxEmbed_coxGen {n k : ℕ} (h : k < n) : coxEmbed n (coxGen n k) = coxGen (n + 1) k := by
  rw [coxGen_of_lt h, coxEmbed_simple, coxGen_of_lt (show k < n + 1 by omega)]
  rfl

/-! ### The coset decomposition -/

/-- Every element of the Coxeter group of type `A_{n+1}` is the product of an element
coming from the Coxeter group of type `A_n` by one of the `n + 2` coset representatives. -/
lemma exists_coxEmbed_mul_cosetRep_step (n : ℕ) (v : (CoxeterMatrix.Aₙ n).Group) (i j : ℕ)
    (hi : i ≤ n + 1) (hj : j < n + 1) :
    ∃ (v' : (CoxeterMatrix.Aₙ n).Group) (i' : ℕ), i' ≤ n + 1 ∧
      coxEmbed n v * cosetRep (n + 1) i * coxGen (n + 1) j
        = coxEmbed n v' * cosetRep (n + 1) i' := by
  set N := n + 1 with hN
  rcases lt_trichotomy (j + 1) (N - i) with hc | hc | hc
  · refine ⟨v * coxGen n j, i, hi, ?_⟩
    rw [map_mul, coxEmbed_coxGen (show j < n by omega), mul_assoc, mul_assoc,
      ← coxGen_mul_cosetRep_comm i j hc]
  · refine ⟨v, i + 1, by omega, ?_⟩
    rw [cosetRep_succ, show N - 1 - i = j by omega, mul_assoc]
  · by_cases heq : j = N - i
    · have hipos : 0 < i := by omega
      refine ⟨v, i - 1, by omega, ?_⟩
      rw [cosetRep_pred hipos, ← heq, mul_assoc, mul_assoc, coxGen_mul_self, mul_one]
    · have hlt : N - i < j := by omega
      refine ⟨v * coxGen n (j - 1), i, hi, ?_⟩
      rw [map_mul, coxEmbed_coxGen (show j - 1 < n by omega), mul_assoc, mul_assoc,
        ← cosetRep_mul_coxGen_of_lt i j hi hlt hj]

theorem exists_coxEmbed_mul_cosetRep (n : ℕ) (w : (CoxeterMatrix.Aₙ (n + 1)).Group) :
    ∃ (v : (CoxeterMatrix.Aₙ n).Group) (i : ℕ), i ≤ n + 1
      ∧ w = coxEmbed n v * cosetRep (n + 1) i := by
  suffices h : ∀ (v : (CoxeterMatrix.Aₙ n).Group) (i : ℕ), i ≤ n + 1 →
      ∃ (v' : (CoxeterMatrix.Aₙ n).Group) (i' : ℕ), i' ≤ n + 1 ∧
        coxEmbed n v * cosetRep (n + 1) i * w = coxEmbed n v' * cosetRep (n + 1) i' by
    obtain ⟨v, i, hi, heq⟩ := h 1 0 (by omega)
    rw [map_one, cosetRep_zero, one_mul, one_mul] at heq
    exact ⟨v, i, hi, heq⟩
  have hmem : w ∈ Submonoid.closure (Set.range (CoxeterMatrix.Aₙ (n + 1)).simple) := by
    rw [← CoxeterMatrix.toCoxeterSystem_simple,
      (CoxeterMatrix.Aₙ (n + 1)).toCoxeterSystem.submonoid_closure_range_simple]
    exact Submonoid.mem_top w
  induction hmem using Submonoid.closure_induction with
  | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      intro v i hi
      have hj : (j : ℕ) < n + 1 := j.isLt
      have : (CoxeterMatrix.Aₙ (n + 1)).simple j = coxGen (n + 1) (j : ℕ) := by
        rw [coxGen_of_lt hj]
      rw [this]
      exact exists_coxEmbed_mul_cosetRep_step n v i j hi hj
  | one => intro v i hi; exact ⟨v, i, hi, by rw [mul_one]⟩
  | mul x y _ _ IHx IHy =>
      intro v i hi
      obtain ⟨v1, i1, hi1, h1⟩ := IHx v i hi
      obtain ⟨v2, i2, hi2, h2⟩ := IHy v1 i1 hi1
      exact ⟨v2, i2, hi2, by rw [← mul_assoc, h1, h2]⟩

/-! ### The action on the last point -/

/-- A transposition of two points in the image of `Fin.castSucc` acts on that image as the
corresponding transposition. -/
lemma swap_castSucc_apply_castSucc (n : ℕ) (a b y : Fin (n + 1)) :
    Equiv.swap a.castSucc b.castSucc y.castSucc = (Equiv.swap a b y).castSucc := by
  by_cases h1 : y = a
  · subst h1; rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
  · by_cases h2 : y = b
    · subst h2; rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
    · rw [Equiv.swap_apply_of_ne_of_ne (fun h => h1 (Fin.castSucc_injective _ h))
        (fun h => h2 (Fin.castSucc_injective _ h)), Equiv.swap_apply_of_ne_of_ne h1 h2]

/-- The image of an element coming from the smaller Coxeter group permutes the points
`Fin.castSucc x` among themselves. -/
lemma permOfCox_coxEmbed_castSucc (n : ℕ) (v : (CoxeterMatrix.Aₙ n).Group) (x : Fin (n + 1)) :
    permOfCox (n + 1) (coxEmbed n v) x.castSucc = (permOfCox n v x).castSucc := by
  revert x
  refine (CoxeterMatrix.Aₙ n).toCoxeterSystem.simple_induction
    (p := fun w => ∀ x : Fin (n + 1),
      permOfCox (n + 1) (coxEmbed n w) x.castSucc = (permOfCox n w x).castSucc) v ?_ ?_ ?_
  · intro i x
    rw [CoxeterMatrix.toCoxeterSystem_simple, coxEmbed_simple, permOfCox_simple,
      permOfCox_simple, adjSwap, adjSwap,
      show (i.castSucc : Fin (n + 1)).succ = (i.succ : Fin (n + 1)).castSucc from Fin.ext rfl,
      swap_castSucc_apply_castSucc]
  · intro x
    simp only [map_one, Equiv.Perm.one_apply]
  · intro w w' hw hw' x
    simp only [map_mul, Equiv.Perm.mul_apply]
    rw [hw', hw]

/-- The image of an element coming from the smaller Coxeter group fixes the last point. -/
lemma permOfCox_coxEmbed_last (n : ℕ) (v : (CoxeterMatrix.Aₙ n).Group) :
    permOfCox (n + 1) (coxEmbed n v) (Fin.last (n + 1)) = Fin.last (n + 1) := by
  refine (CoxeterMatrix.Aₙ n).toCoxeterSystem.simple_induction
    (p := fun w => permOfCox (n + 1) (coxEmbed n w) (Fin.last (n + 1)) = Fin.last (n + 1))
    v ?_ ?_ ?_
  · intro i
    rw [CoxeterMatrix.toCoxeterSystem_simple, coxEmbed_simple, permOfCox_simple, adjSwap]
    refine Equiv.swap_apply_of_ne_of_ne (Fin.ne_of_val_ne ?_) (Fin.ne_of_val_ne ?_)
    · have : ((i.castSucc : Fin (n + 1)).castSucc : ℕ) = (i : ℕ) := rfl
      rw [this, Fin.val_last]
      omega
    · have : ((i.castSucc : Fin (n + 1)).succ : ℕ) = (i : ℕ) + 1 := rfl
      rw [this, Fin.val_last]
      omega
  · simp only [map_one, Equiv.Perm.one_apply]
  · intro w w' hw hw'
    simp only [map_mul, Equiv.Perm.mul_apply]
    rw [hw', hw]

/-- The image of a nontrivial coset representative sends the last point to the point
before it. -/
lemma permOfCox_cosetRep_last (N : ℕ) : ∀ i : ℕ, 0 < i → i ≤ N →
    ((permOfCox N (cosetRep N i) (Fin.last N) : Fin (N + 1)) : ℕ) = N - 1 := by
  intro i
  induction i with
  | zero => intro h; omega
  | succ i IH =>
      intro _ hiN
      rw [cosetRep_succ, map_mul, Equiv.Perm.mul_apply,
        permOfCox_coxGen (show N - 1 - i < N by omega), adjSwap]
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · rw [cosetRep_zero, map_one, Equiv.Perm.one_apply]
        have hlast : (⟨N - 1 - 0, show N - 1 - 0 < N by omega⟩ : Fin N).succ = Fin.last N :=
          Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega)
        rw [← hlast, Equiv.swap_apply_right]
        rfl
      · have hfix : Equiv.swap (⟨N - 1 - i, show N - 1 - i < N by omega⟩ : Fin N).castSucc
            (⟨N - 1 - i, show N - 1 - i < N by omega⟩ : Fin N).succ (Fin.last N)
            = Fin.last N := by
          refine Equiv.swap_apply_of_ne_of_ne (Fin.ne_of_val_ne ?_) (Fin.ne_of_val_ne ?_)
          · have : ((⟨N - 1 - i, show N - 1 - i < N by omega⟩ : Fin N).castSucc : ℕ)
                = N - 1 - i := rfl
            rw [this, Fin.val_last]
            omega
          · have : ((⟨N - 1 - i, show N - 1 - i < N by omega⟩ : Fin N).succ : ℕ)
                = N - 1 - i + 1 := rfl
            rw [this, Fin.val_last]
            omega
        rw [hfix]
        exact IH hipos (by omega)

/-- A nontrivial coset representative moves the last point. -/
lemma permOfCox_cosetRep_last_ne (N i : ℕ) (hN : 0 < N) (hi : 0 < i) (hiN : i ≤ N) :
    permOfCox N (cosetRep N i) (Fin.last N) ≠ Fin.last N := by
  intro h
  have hval := permOfCox_cosetRep_last N i hi hiN
  rw [h, Fin.val_last] at hval
  omega

/-! ### Injectivity -/

theorem permOfCox_injective (n : ℕ) : Function.Injective (permOfCox n) := by
  induction n with
  | zero =>
      have htriv : ∀ w : (CoxeterMatrix.Aₙ 0).Group, w = 1 := by
        intro w
        refine (CoxeterMatrix.Aₙ 0).toCoxeterSystem.simple_induction (p := fun w => w = 1) w
          (fun i => i.elim0) rfl ?_
        intro a b ha hb
        rw [ha, hb, mul_one]
      intro a b _
      rw [htriv a, htriv b]
  | succ n IH =>
      rw [injective_iff_map_eq_one]
      intro w hw
      obtain ⟨v, i, hi, rfl⟩ := exists_coxEmbed_mul_cosetRep n w
      have hi0 : i = 0 := by
        by_contra h0
        have hpos : 0 < i := Nat.pos_of_ne_zero h0
        rw [map_mul] at hw
        have happ := congrArg (fun sigma : Equiv.Perm (Fin (n + 2)) => sigma (Fin.last (n + 1))) hw
        simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at happ
        have hfix := permOfCox_coxEmbed_last n v
        have hx := (permOfCox (n + 1) (coxEmbed n v)).injective (happ.trans hfix.symm)
        exact permOfCox_cosetRep_last_ne (n + 1) i (by omega) hpos hi hx
      subst hi0
      rw [cosetRep_zero, mul_one] at hw ⊢
      have hv1 : permOfCox n v = 1 := by
        refine Equiv.ext fun x => ?_
        have hcs := permOfCox_coxEmbed_castSucc n v x
        rw [hw, Equiv.Perm.one_apply] at hcs
        exact (Fin.castSucc_injective _ hcs).symm
      rw [(injective_iff_map_eq_one _).1 IH v hv1, map_one]

theorem permOfCox_bijective (n : ℕ) : Function.Bijective (permOfCox n) :=
  ⟨permOfCox_injective n, permOfCox_surjective n⟩

/-- **The symmetric group is the Coxeter group of type `Aₙ`**: the Coxeter system on
`Equiv.Perm (Fin (n + 1))` whose simple reflections are the adjacent transpositions. -/
noncomputable def permCoxeterSystem (n : ℕ) :
    CoxeterSystem (CoxeterMatrix.Aₙ n) (Equiv.Perm (Fin (n + 1))) :=
  ⟨(MulEquiv.ofBijective (permOfCox n) (permOfCox_bijective n)).symm⟩

@[simp] lemma permCoxeterSystem_simple (n : ℕ) (i : Fin n) :
    (permCoxeterSystem n).simple i = adjSwap n i :=
  permOfCox_simple n i

instance instIsCoxeterGroupPerm (n : ℕ) : IsCoxeterGroup (Equiv.Perm (Fin (n + 1))) :=
  ⟨⟨Fin n, CoxeterMatrix.Aₙ n, ⟨permCoxeterSystem n⟩⟩⟩

end Equiv.Perm
