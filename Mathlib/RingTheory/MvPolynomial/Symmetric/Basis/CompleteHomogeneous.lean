/-
Copyright (c) 2026 Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/
import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.Pieri
import Mathlib.RingTheory.MvPolynomial.Symmetric.Schur.Basis

/-!
# The products of complete homogeneous symmetric polynomials form a basis

Following `theories/MPoly/sympoly.v` of
[Coq-Combi](https://github.com/math-comp/Coq-Combi), we prove the expansion of a product
`h_lam = h_{lam_1} * ... * h_{lam_k}` of complete homogeneous symmetric polynomials in the
basis of Schur polynomials, `h_lam = ∑_mu K_{mu lam} s_mu`, where `K_{mu lam}` is the
Kostka number counting the tableaux of shape `mu` and content `lam`.  Since the Kostka
numbers are unitriangular for the dominance order, the polynomials `h_lam`, for `lam` a
partition of `n` with at most `m` parts, form a basis of the module of symmetric
homogeneous polynomials of degree `n` in `m` variables.

## Main results

* `MvPolynomial.hProd_eq_sum_kostka` : `h_lam = ∑_mu K_{mu lam} s_mu`.
* `MvPolynomial.linearIndependent_hProd` : the `h_lam` are linearly independent.
* `MvPolynomial.span_hProd` : they span the symmetric homogeneous polynomials of degree `n`.
* `MvPolynomial.hBasis` : the resulting basis.
-/

namespace MvPolynomial

open List MvPolynomial

variable {m : ℕ} {R : Type*}

/-! ### Kostka numbers: elementary properties -/

/-- There is exactly one tableau of empty shape, and it has empty content. -/
lemma kostkaNum_nil {N : ℕ} {c : ℕ → ℕ} (h : ∀ i, i < N → c i = 0) :
    kostkaNum N [] c = 1 := by
  rw [kostkaNum, Nat.card_eq_one_iff_exists]
  refine ⟨⟨[], ?_⟩, ?_⟩
  · refine ⟨?_, rfl, by simp, fun i hi => by simpa using (h i hi).symm⟩
    simp [IsTableau]
  · rintro ⟨P, hP, hsh, -, -⟩
    refine Subtype.ext ?_
    have : P.map List.length = [] := hsh
    simpa using this

/-! ### The content of a list, as a function -/

/-- The content function attached to a list: `i ↦ lam.getD i 0`. -/
def contentOf (lam : List ℕ) : ℕ → ℕ := fun i => lam.getD i 0

@[simp] lemma contentOf_apply (lam : List ℕ) (i : ℕ) : contentOf lam i = lam.getD i 0 := rfl

lemma contentOf_append_singleton_of_lt {lam : List ℕ} {r i : ℕ} (hi : i < lam.length) :
    contentOf (lam ++ [r]) i = contentOf lam i := by
  simp [contentOf, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma contentOf_append_singleton_self (lam : List ℕ) (r : ℕ) :
    contentOf (lam ++ [r]) lam.length = r := by
  simp [contentOf, List.getD_eq_getElem?_getD]

/-! ### The product of complete homogeneous symmetric polynomials -/

/-- The product `h_lam = h_{lam_1} * ... * h_{lam_k}` of complete homogeneous symmetric
polynomials attached to a list `lam`. -/
noncomputable def hProd (m : ℕ) (R : Type*) [CommRing R] (lam : List ℕ) :
    MvPolynomial (Fin m) R := (lam.map (hsymm (Fin m) R)).prod

@[simp] lemma hProd_nil (m : ℕ) (R : Type*) [CommRing R] : hProd m R [] = 1 := rfl

lemma hProd_append_singleton (m : ℕ) (R : Type*) [CommRing R] (lam : List ℕ) (r : ℕ) :
    hProd m R (lam ++ [r]) = hProd m R lam * hsymm (Fin m) R r := by
  simp [hProd]

/-- **The Pieri recursion determines the Kostka expansion**: if a family `F` of
polynomials indexed by partitions satisfies the Pieri rule for a family `H` of
multipliers, then the product `H_{lam_1} * ⋯ * H_{lam_k} * F []` expands with the Kostka
numbers as coefficients.  Applied to `H = h` and to the Schur polynomials, this is the
expansion `h_lam = ∑_mu K_{mu lam} s_mu`. -/
theorem pieriProd_mul_eq_sum_kostkaNum [CommRing R] (m : ℕ) (H : ℕ → MvPolynomial (Fin m) R)
    (F : List ℕ → MvPolynomial (Fin m) R)
    (hF : ∀ mu : List ℕ, IsPart mu → ∀ r : ℕ, F mu * H r
      = ∑ nu ∈ partFinset (mu.sum + r), if HorizStrip nu mu then F nu else 0)
    (lam : List ℕ) :
    (lam.map H).prod * F []
      = ∑ mu ∈ partFinset lam.sum,
          (kostkaNum lam.length mu (contentOf lam) : R) • F mu := by
  classical
  induction lam using List.reverseRecOn with
  | nil =>
    rw [List.map_nil, List.prod_nil, List.sum_nil, partFinset_zero, Finset.sum_singleton,
      kostkaNum_nil (fun i hi => absurd hi (by simp))]
    simp
  | append_singleton lam r ih =>
    have hsum : (lam ++ [r]).sum = lam.sum + r := by simp
    have hlen : (lam ++ [r]).length = lam.length + 1 := by simp
    have hcontent : ∀ mu : List ℕ,
        kostkaNum lam.length mu (contentOf (lam ++ [r]))
          = kostkaNum lam.length mu (contentOf lam) :=
      fun mu => kostkaNum_congr _ _ fun i hi => contentOf_append_singleton_of_lt hi
    have hprod : ((lam ++ [r]).map H).prod = (lam.map H).prod * H r := by simp
    rw [hprod, mul_right_comm, ih, Finset.sum_mul, hsum, hlen]
    have hstep : ∀ mu ∈ partFinset lam.sum,
        ((kostkaNum lam.length mu (contentOf lam) : R) • F mu) * H r
          = ∑ nu ∈ partFinset (lam.sum + r),
              if HorizStrip nu mu then
                (kostkaNum lam.length mu (contentOf lam) : R) • F nu else 0 := by
      intro mu hmu
      obtain ⟨hmupart, hmusum⟩ := mem_partFinset.1 hmu
      rw [smul_mul_assoc, hF mu hmupart r, hmusum, Finset.smul_sum]
      exact Finset.sum_congr rfl fun nu _ => by split_ifs <;> simp
    rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
    refine Finset.sum_congr rfl fun nu hnu => ?_
    obtain ⟨hnupart, hnusum⟩ := mem_partFinset.1 hnu
    have hkey : kostkaNum (lam.length + 1) nu (contentOf (lam ++ [r]))
        = ∑ mu ∈ partFinset lam.sum,
            if HorizStrip nu mu then kostkaNum lam.length mu (contentOf lam) else 0 := by
      have := kostkaNum_succ (N := lam.length) (sh := nu) (c := contentOf (lam ++ [r]))
        (m := lam.sum) hnupart (by rw [contentOf_append_singleton_self, hnusum])
      rw [this, sum_subtype_eq_sum_partFinset lam.sum
        (fun p => if HorizStrip nu p then kostkaNum lam.length p (contentOf (lam ++ [r])) else 0)]
      exact Finset.sum_congr rfl fun mu _ => by rw [hcontent mu]
    rw [hkey, Nat.cast_sum, Finset.sum_smul]
    exact Finset.sum_congr rfl fun mu _ => by split_ifs <;> simp

/-- The Pieri recursion determines the Kostka expansion, for the products `h_lam` of
complete homogeneous symmetric polynomials. -/
theorem hProd_mul_eq_sum_kostkaNum [CommRing R] (m : ℕ) (F : List ℕ → MvPolynomial (Fin m) R)
    (hF : ∀ mu : List ℕ, IsPart mu → ∀ r : ℕ, F mu * hsymm (Fin m) R r
      = ∑ nu ∈ partFinset (mu.sum + r), if HorizStrip nu mu then F nu else 0)
    (lam : List ℕ) :
    hProd m R lam * F []
      = ∑ mu ∈ partFinset lam.sum,
          (kostkaNum lam.length mu (contentOf lam) : R) • F mu :=
  pieriProd_mul_eq_sum_kostkaNum m (hsymm (Fin m) R) F hF lam

/-- **The expansion of `h_lam` in the Schur polynomials**: `h_lam = ∑_mu K_{mu lam} s_mu`,
where the Kostka number `K_{mu lam}` counts the tableaux of shape `mu` and content
`lam`. -/
theorem hProd_eq_sum_kostkaNum [CommRing R] (m : ℕ) (lam : List ℕ) :
    hProd m R lam
      = ∑ mu ∈ partFinset lam.sum,
          (kostkaNum lam.length mu (contentOf lam) : R) • schurPoly (Fin m) R mu := by
  have := hProd_mul_eq_sum_kostkaNum (R := R) m (schurPoly (Fin m) R)
    (fun mu hmu r => schurPoly_mul_hsymm m hmu r) lam
  rwa [schurPoly_nil, mul_one] at this

/-- `h_lam` is a symmetric homogeneous polynomial of degree `|lam|`. -/
lemma hProd_mem_symHomogeneousSubmodule' [CommRing R] (lam : List ℕ) :
    hProd m R lam ∈ symHomogeneousSubmodule m lam.sum R := by
  induction lam with
  | nil => exact ⟨isHomogeneous_one (Fin m) R, IsSymmetric.one⟩
  | cons a l ih =>
    have hcons : hProd m R (a :: l) = hsymm (Fin m) R a * hProd m R l := by simp [hProd]
    have hrow : hsymm (Fin m) R a = schurPoly (Fin m) R (rowShape a) :=
      (schurPoly_rowShape (Fin m) R a).symm
    obtain ⟨hhom, hsym⟩ := ih
    refine ⟨?_, ?_⟩
    · rw [hcons, hrow]
      have := (isHomogeneous_schurPoly_of_sum (m := m) (R := R) (n := a)
        (sum_rowShape a)).mul hhom
      simpa [List.sum_cons] using this
    · rw [hcons, hrow]
      exact (schurPoly_isSymmetric _).mul hsym

/-- `h_lam` is a symmetric homogeneous polynomial of degree `|lam|`. -/
lemma hProd_mem_symHomogeneousSubmodule [CommRing R] {n : ℕ} (lam : PartIdx n m) :
    hProd m R lam.1 ∈ symHomogeneousSubmodule m n R := by
  have := hProd_mem_symHomogeneousSubmodule' (m := m) (R := R) lam.1
  rwa [lam.2.2.1] at this

/-! ### The bridge with the Kostka numbers of `Combinatorics/Young/Tableau/Kostka.lean` -/

/-- A letter occurs as often in the reading word of a tableau as in its list of boxes. -/
lemma count_toWord_eq_count_flatten (t : List (List ℕ)) (i : ℕ) :
    (toWord t).count i = t.flatten.count i :=
  ((List.reverse_perm t).flatten).count_eq i

/-- The two definitions of the Kostka numbers agree: the number of tableaux of shape `mu`
with letters `< lam.length` and content `lam` is the number of tableaux of shape `mu`
whose reading word has evaluation `lam`. -/
theorem kostkaNum_eq_kostka {lam : List ℕ} (hlam : IsPart lam) (mu : List ℕ) :
    kostkaNum lam.length mu (contentOf lam) = kostka mu lam := by
  rw [kostkaNum, kostka]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun t => ?_)
  simp only [tabSet, Set.mem_setOf_eq, contentOf_apply]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · rintro ⟨hlt, hcount⟩
    refine ext_getD_of_getLastD_ne_zero (getLastD_evalseq_ne_zero _) hlam.getLastD_ne_zero
      fun i => ?_
    rw [getD_evalseq, count_toWord_eq_count_flatten]
    rcases lt_or_ge i lam.length with hi | hi
    · exact hcount i hi
    · rw [List.getD_eq_default _ _ hi, List.count_eq_zero]
      intro hmem
      exact absurd (hlt i hmem) (by omega)
  · intro hev
    have hgetD : ∀ i, t.flatten.count i = lam.getD i 0 := by
      intro i
      rw [← count_toWord_eq_count_flatten, ← getD_evalseq, hev]
    refine ⟨fun x hx => ?_, fun i _ => hgetD i⟩
    by_contra hxlt
    have hzero : lam.getD x 0 = 0 := List.getD_eq_default _ _ (by omega)
    have hpos : 0 < t.flatten.count x := List.count_pos_iff.2 hx
    rw [hgetD x, hzero] at hpos
    exact absurd hpos (by omega)

/-- The expansion of `h_lam` in the Schur polynomials, with the Kostka numbers of
`Combinatorics/Young/Tableau/Kostka.lean`. -/
theorem hProd_eq_sum_kostka [CommRing R] (m : ℕ) {lam : List ℕ} (hlam : IsPart lam) :
    hProd m R lam
      = ∑ mu ∈ partFinset lam.sum, (kostka mu lam : R) • schurPoly (Fin m) R mu := by
  rw [hProd_eq_sum_kostkaNum]
  exact Finset.sum_congr rfl fun mu _ => by rw [kostkaNum_eq_kostka hlam mu]

/-- The expansion of `h_lam`, restricted to the shapes with at most `m` rows: the Schur
polynomials of the other shapes vanish in `m` variables. -/
theorem hProd_eq_sum_partsFinset [CommRing R] (m : ℕ) {lam : List ℕ} (hlam : IsPart lam) :
    hProd m R lam
      = ∑ mu ∈ partsFinset lam.sum m, (kostka mu lam : R) • schurPoly (Fin m) R mu := by
  classical
  rw [hProd_eq_sum_kostka m hlam]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro mu hmu
    obtain ⟨h1, h2, -⟩ := mem_partsFinset.1 hmu
    exact mem_partFinset.2 ⟨h1, h2⟩
  · intro mu hmu hnot
    have hlen : m < mu.length := by
      by_contra hle
      obtain ⟨h1, h2⟩ := mem_partFinset.1 hmu
      exact hnot (mem_partsFinset.2 ⟨h1, h2, by omega⟩)
    rw [schurPoly_eq_zero_of_lt_length hlen, smul_zero]

/-! ### Linear independence -/

/-- A Kostka number `K_{mu lam}` is nonzero only if `mu` dominates `lam`. -/
lemma partdom_of_kostka_ne_zero {mu lam : List ℕ} (h : kostka mu lam ≠ 0) : Partdom lam mu := by
  by_contra hdom
  exact h (kostka_eq_zero_of_not_partdom hdom)

/-- The expansion of `h_lam` in the Schur polynomials, indexed by `PartIdx n m`. -/
lemma hProd_eq_sum_partIdx [CommRing R] {n : ℕ} (lam : PartIdx n m) :
    hProd m R lam.1
      = ∑ nu : PartIdx n m, (kostka nu.1 lam.1 : R) • schurPoly (Fin m) R nu.1 := by
  classical
  rw [hProd_eq_sum_partsFinset m lam.2.1, lam.2.2.1, partsFinset,
    Finset.sum_image fun x _ y _ h => Subtype.ext h]

/-- **The products `h_lam` are linearly independent**: over any commutative ring, the
polynomials `h_lam` for `lam` a partition of `n` with at most `m` parts are linearly
independent. -/
theorem linearIndependent_hProd (m n : ℕ) (R : Type*) [CommRing R] :
    LinearIndependent R fun lam : PartIdx n m => hProd m R lam.1 := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg lam
  have hexp : ∑ mu : PartIdx n m, g mu • hProd m R mu.1
      = ∑ nu : PartIdx n m,
          (∑ mu : PartIdx n m, g mu * (kostka nu.1 mu.1 : R)) • schurPoly (Fin m) R nu.1 := by
    simp only [hProd_eq_sum_partIdx, Finset.smul_sum, Finset.sum_smul, smul_smul]
    exact Finset.sum_comm
  have hcoef : ∀ nu : PartIdx n m, ∑ mu : PartIdx n m, g mu * (kostka nu.1 mu.1 : R) = 0 :=
    Fintype.linearIndependent_iff.1 (linearIndependent_schurPoly m n R) _ (by rw [← hexp, hg])
  by_contra hne
  obtain ⟨nu, hnut, hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter fun mu : PartIdx n m => g mu ≠ 0) (fun mu => domWeight n mu.1)
    ⟨lam, Finset.mem_filter.2 ⟨Finset.mem_univ _, hne⟩⟩
  obtain ⟨-, hnu0⟩ := Finset.mem_filter.1 hnut
  have hsingle : ∀ mu ∈ (Finset.univ : Finset (PartIdx n m)), mu ≠ nu →
      g mu * (kostka nu.1 mu.1 : R) = 0 := by
    intro mu _ hmune
    by_cases hgmu : g mu = 0
    · rw [hgmu, zero_mul]
    · have hmut : mu ∈ Finset.univ.filter fun mu : PartIdx n m => g mu ≠ 0 :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hgmu⟩
      have hzero : kostka nu.1 mu.1 = 0 := by
        by_contra hk
        have hdom : Partdom mu.1 nu.1 := partdom_of_kostka_ne_zero hk
        exact hmune (Subtype.ext (eq_of_partdom_of_domWeight_eq mu.2.1 nu.2.1 mu.2.2.1
          nu.2.2.1 hdom (hmin mu hmut)))
      rw [hzero, Nat.cast_zero, mul_zero]
  have := hcoef nu
  rw [Finset.sum_eq_single nu hsingle (fun h => absurd (Finset.mem_univ nu) h),
    kostka_self nu.2.1, Nat.cast_one, mul_one] at this
  exact hnu0 this

/-! ### Spanning -/

/-- Every Schur polynomial of a partition of `n` with at most `m` parts is a linear
combination of the products `h_lam`. -/
theorem schurPoly_mem_span_hProd [CommRing R] (n : ℕ) {lam : List ℕ} (hlam : IsPart lam)
    (hsum : lam.sum = n) (hlen : lam.length ≤ m) :
    schurPoly (Fin m) R lam
      ∈ Submodule.span R (Set.range fun mu : PartIdx n m => hProd m R mu.1) := by
  classical
  set W := Submodule.span R (Set.range fun mu : PartIdx n m => hProd m R mu.1) with hW
  suffices H : ∀ k : ℕ, ∀ nu : List ℕ, IsPart nu → nu.sum = n → nu.length ≤ m →
      (n + 1) * n - domWeight n nu ≤ k → schurPoly (Fin m) R nu ∈ W by
    exact H _ lam hlam hsum hlen le_rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro nu hnu hnusum hnulen hk
    have hexp := hProd_eq_sum_partsFinset (R := R) m hnu
    rw [hnusum] at hexp
    have hmem : nu ∈ partsFinset n m := mem_partsFinset.2 ⟨hnu, hnusum, hnulen⟩
    have hsplit := Finset.add_sum_erase (partsFinset n m)
      (fun mu => (kostka mu nu : R) • schurPoly (Fin m) R mu) hmem
    simp only [kostka_self hnu, Nat.cast_one, one_smul] at hsplit
    have hrest : ∀ mu ∈ (partsFinset n m).erase nu,
        (kostka mu nu : R) • schurPoly (Fin m) R mu ∈ W := by
      intro mu hmu
      have hmune : mu ≠ nu := Finset.ne_of_mem_erase hmu
      obtain ⟨hmupart, hmusum, hmulen⟩ := mem_partsFinset.1 (Finset.mem_of_mem_erase hmu)
      by_cases hk0 : kostka mu nu = 0
      · rw [hk0, Nat.cast_zero, zero_smul]
        exact Submodule.zero_mem _
      · have hdom : Partdom nu mu := partdom_of_kostka_ne_zero hk0
        have hlt : domWeight n nu < domWeight n mu := by
          rcases lt_or_eq_of_le (domWeight_le_domWeight (n := n) hdom) with h | h
          · exact h
          · exact absurd (eq_of_partdom_of_domWeight_eq hnu hmupart hnusum hmusum hdom
              (le_of_eq h.symm)).symm hmune
        have hbd : domWeight n mu ≤ (n + 1) * n := by
          rw [domWeight]
          calc ∑ j ∈ Finset.range (n + 1), (mu.take j).sum
              ≤ ∑ _j ∈ Finset.range (n + 1), n :=
                Finset.sum_le_sum fun j _ => hmusum ▸ sum_take_le_sum mu j
            _ = (n + 1) * n := by simp [mul_comm]
        exact Submodule.smul_mem _ _
          (ih ((n + 1) * n - domWeight n mu) (by omega) mu hmupart hmusum hmulen le_rfl)
    have hkey : schurPoly (Fin m) R nu
        = hProd m R nu - ∑ mu ∈ (partsFinset n m).erase nu,
            (kostka mu nu : R) • schurPoly (Fin m) R mu :=
      eq_sub_of_add_eq (hsplit.trans hexp.symm)
    rw [hkey]
    exact Submodule.sub_mem _ (Submodule.subset_span ⟨⟨nu, hnu, hnusum, hnulen⟩, rfl⟩)
      (Submodule.sum_mem _ hrest)

/-- **The products `h_lam` span** the module of symmetric homogeneous polynomials of
degree `n` in `m` variables. -/
theorem span_hProd [CommRing R] (m n : ℕ) :
    Submodule.span R (Set.range fun lam : PartIdx n m => hProd m R lam.1)
      = symHomogeneousSubmodule m n R := by
  refine le_antisymm (Submodule.span_le.2 ?_) ?_
  · rintro q ⟨lam, rfl⟩
    exact hProd_mem_symHomogeneousSubmodule lam
  · rw [← span_schurPoly m n]
    refine Submodule.span_le.2 ?_
    rintro q ⟨nu, rfl⟩
    exact schurPoly_mem_span_hProd n nu.2.1 nu.2.2.1 nu.2.2.2

/-- The product `h_lam`, as an element of the module of symmetric homogeneous polynomials
of degree `n`. -/
noncomputable def hSub (m n : ℕ) (R : Type*) [CommRing R] (lam : PartIdx n m) :
    symHomogeneousSubmodule m n R :=
  ⟨hProd m R lam.1, hProd_mem_symHomogeneousSubmodule lam⟩

@[simp] lemma coe_hSub (m n : ℕ) (R : Type*) [CommRing R] (lam : PartIdx n m) :
    (hSub m n R lam : MvPolynomial (Fin m) R) = hProd m R lam.1 := rfl

lemma linearIndependent_hSub (m n : ℕ) (R : Type*) [CommRing R] :
    LinearIndependent R (hSub m n R) :=
  LinearIndependent.of_comp (symHomogeneousSubmodule m n R).subtype
    (linearIndependent_hProd m n R)

lemma span_hSub (m n : ℕ) (R : Type*) [CommRing R] :
    ⊤ ≤ Submodule.span R (Set.range (hSub m n R)) := by
  intro p _
  have hmap : Submodule.map (symHomogeneousSubmodule m n R).subtype
      (Submodule.span R (Set.range (hSub m n R))) = symHomogeneousSubmodule m n R := by
    rw [Submodule.map_span, ← Set.range_comp]
    exact span_hProd m n
  have hp : (p : MvPolynomial (Fin m) R) ∈ Submodule.map
      (symHomogeneousSubmodule m n R).subtype
      (Submodule.span R (Set.range (hSub m n R))) := by
    rw [hmap]
    exact p.2
  obtain ⟨q, hq, hqp⟩ := hp
  have hqp' : q = p := Subtype.ext hqp
  rwa [hqp'] at hq

/-- **The products of complete homogeneous symmetric polynomials form a basis** of the
module of symmetric homogeneous polynomials of degree `n` in `m` variables, indexed by the
partitions of `n` with at most `m` parts. -/
noncomputable def hBasis (m n : ℕ) (R : Type*) [CommRing R] :
    Module.Basis (PartIdx n m) R (symHomogeneousSubmodule m n R) :=
  Module.Basis.mk (linearIndependent_hSub m n R) (span_hSub m n R)

lemma coe_hBasis (m n : ℕ) (R : Type*) [CommRing R] (lam : PartIdx n m) :
    (hBasis m n R lam : MvPolynomial (Fin m) R) = hProd m R lam.1 := by
  rw [hBasis, Module.Basis.mk_apply, coe_hSub]

end MvPolynomial
