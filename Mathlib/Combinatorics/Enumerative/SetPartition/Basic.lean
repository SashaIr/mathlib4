/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.Order.Partition.Finpartition
import Mathlib.Combinatorics.Enumerative.SetPartition.Ordered

/-!
# Counting set partitions with prescribed block sizes

Ported from the Coq-Combi development (`Combi/set_partition.v`).

## Main definitions

* `Finpartition.partShape P` : the shape of a `Finpartition`, i.e. the multiset of the
  cardinalities of its blocks.
* `Finpartition.shapeParts s m` : the finset of the set partitions of `s` of shape `m`.

## Main results

* `Finpartition.card_shapeParts` : the number of set partitions of a finite set `s` whose blocks
  have cardinalities given by a multiset `m` of positive integers with `m.sum = |s|` is
  Mathlib's `Multiset.bell m`.  (Mathlib defines `Multiset.bell` by an explicit formula
  and leaves the combinatorial interpretation as an open TODO.)
* `Finpartition.card_shapeParts_replicate` : the case of blocks all of the same size, counted by
  `Nat.uniformBell`.
-/

namespace Finpartition

open Finset

/-! ### Indexing a list of known length -/

/-- The entries of a list of known length `n`, as a function on `Fin n`. -/
def listFun {β : Type*} (L : List β) {n : ℕ} (h : L.length = n) (i : Fin n) : β :=
  L[(i : ℕ)]'(by omega)

lemma ofFn_listFun {β : Type*} (L : List β) {n : ℕ} (h : L.length = n) :
    List.ofFn (listFun L h) = L := by
  apply List.ext_getElem (by simp [h])
  intro i h1 h2
  simp [listFun]

lemma listFun_injective {β : Type*} {L : List β} {n : ℕ} (h : L.length = n) (hL : L.Nodup) :
    Function.Injective (listFun L h) := by
  intro i j hij
  simp only [listFun] at hij
  have := (List.Nodup.getElem_inj_iff hL).1 hij
  exact Fin.ext this

lemma map_listFun {β γ : Type*} (L : List β) {n : ℕ} (h : L.length = n) (c : β → γ) :
    List.ofFn (c ∘ listFun L h) = L.map c := by
  rw [← List.map_ofFn, ofFn_listFun]

/-! ### Permutation invariance of the data defining an ordered set partition -/

variable {α : Type*} [DecidableEq α]

lemma listUnion_perm {L L' : List (Finset α)} (hp : L.Perm L') : listUnion L = listUnion L' := by
  ext a
  simp only [mem_listUnion]
  exact ⟨fun ⟨B, hB, ha⟩ => ⟨B, hp.mem_iff.1 hB, ha⟩, fun ⟨B, hB, ha⟩ => ⟨B, hp.mem_iff.2 hB, ha⟩⟩

omit [DecidableEq α] in
lemma pairwise_disjoint_perm {L L' : List (Finset α)} (hp : L.Perm L')
    (h : L.Pairwise Disjoint) : L'.Pairwise Disjoint := by
  have hs : ∀ ⦃A B : Finset α⦄, Disjoint A B → Disjoint B A := fun _ _ hd => hd.symm
  exact hp.pairwise h (fun {_ _} hd => hs hd)

/-- Inside `orderedParts s l` with no zero size, the blocks are pairwise distinct. -/
lemma nodup_of_mem_orderedParts {s : Finset α} {l : List ℕ} {L : List (Finset α)}
    (hL : L ∈ orderedParts s l) (h0 : (0 : ℕ) ∉ l) : L.Nodup := by
  obtain ⟨hmap, hpw, -⟩ := mem_orderedParts.1 hL
  have hne : ∀ B ∈ L, B ≠ ∅ := by
    intro B hB hB0
    refine h0 ?_
    rw [← hmap]
    have := List.mem_map_of_mem (f := Finset.card) hB
    rwa [hB0, Finset.card_empty] at this
  change List.Pairwise (· ≠ ·) L
  refine List.Pairwise.imp_of_mem (fun {B C} hB _ hd => ?_) hpw
  rintro rfl
  exact hne B hB (by simpa using disjoint_self.mp hd)

/-! ### The shape of a finite partition -/

/-- The multiset of the cardinalities of the blocks of a finite partition. -/
def partShape {s : Finset α} (P : Finpartition s) : Multiset ℕ := P.parts.val.map Finset.card

/-- The finset of set partitions of `s` whose blocks have cardinalities given by `m`. -/
def shapeParts (s : Finset α) (m : Multiset ℕ) : Finset (Finpartition s) :=
  Finset.univ.filter fun P => partShape P = m

lemma mem_shapeParts {s : Finset α} {m : Multiset ℕ} {P : Finpartition s} :
    P ∈ shapeParts s m ↔ partShape P = m := by simp [shapeParts]

/-- The blocks of a list in `orderedParts` form a set partition of the prescribed shape. -/
lemma exists_finpartition_of_mem_orderedParts {s : Finset α} {l : List ℕ}
    {L : List (Finset α)} (hL : L ∈ orderedParts s l) (h0 : (0 : ℕ) ∉ l) :
    ∃ P : Finpartition s, P.parts = L.toFinset ∧ partShape P = (l : Multiset ℕ) := by
  obtain ⟨hmap, hpw, hun⟩ := mem_orderedParts.1 hL
  have hnd : L.Nodup := nodup_of_mem_orderedParts hL h0
  have hne : ∀ B ∈ L, B ≠ ∅ := by
    intro B hB hB0
    refine h0 ?_
    rw [← hmap]
    have := List.mem_map_of_mem (f := Finset.card) hB
    rwa [hB0, Finset.card_empty] at this
  have hsup : L.toFinset.sup id = s := by
    ext a
    rw [Finset.mem_sup]
    simp only [id_eq, List.mem_toFinset, ← hun, mem_listUnion]
  refine ⟨⟨L.toFinset, ?_, hsup, ?_⟩, rfl, ?_⟩
  · refine Finset.supIndep_iff_pairwiseDisjoint.2 ?_
    intro B hB C hC hBC
    simp only [Finset.mem_coe, List.mem_toFinset] at hB hC
    exact hpw.forall hB hC hBC
  · simp only [List.mem_toFinset]
    intro hbot
    exact hne ⊥ hbot rfl
  · change (L.toFinset).val.map Finset.card = (l : Multiset ℕ)
    rw [List.toFinset_val, hnd.dedup, ← hmap]
    rfl

/-- Every set partition of the prescribed shape arises from a list in `orderedParts`. -/
lemma exists_mem_orderedParts_of_shape {s : Finset α} {l : List ℕ}
    {P : Finpartition s} (hP : partShape P = (l : Multiset ℕ)) :
    ∃ L ∈ orderedParts s l, L.toFinset = P.parts := by
  have hperm : (l : Multiset ℕ) = ↑(P.parts.toList.map Finset.card) := by
    rw [← hP]
    change P.parts.val.map Finset.card = _
    rw [← Finset.coe_toList P.parts]
    rfl
  have hp : l.Perm (P.parts.toList.map Finset.card) := Multiset.coe_eq_coe.1 hperm
  have hcomp : Relation.Comp (fun x1 x2 => x1 = List.map Finset.card x2)
      (fun x1 x2 => x1.Perm x2) l P.parts.toList := by
    rw [List.eq_map_comp_perm]
    exact hp
  obtain ⟨L, hLmap, hLperm⟩ := hcomp
  have hnd : L.Nodup := hLperm.nodup_iff.2 (Finset.nodup_toList P.parts)
  have htf : L.toFinset = P.parts := by
    ext a
    simp only [List.mem_toFinset, hLperm.mem_iff, Finset.mem_toList]
  refine ⟨L, mem_orderedParts.2 ⟨hLmap.symm, ?_, ?_⟩, htf⟩
  · refine hnd.pairwise_of_forall_ne ?_
    intro B hB C hC hBC
    have := Finset.supIndep_iff_pairwiseDisjoint.1 P.supIndep
    exact this (by simpa [← htf] using hB) (by simpa [← htf] using hC) hBC
  · ext a
    rw [mem_listUnion, ← P.sup_parts, Finset.mem_sup]
    simp only [id_eq, ← htf, List.mem_toFinset]

/-- The number of ways to enumerate the blocks of a fixed set partition so that the
sizes come out in a prescribed order. -/
lemma card_fiber_orderedParts {s : Finset α} {l : List ℕ} {P : Finpartition s}
    (hP : partShape P = (l : Multiset ℕ)) (h0 : (0 : ℕ) ∉ l) :
    ((orderedParts s l).filter fun L => L.toFinset = P.parts).card
      = ∏ k ∈ l.toFinset, Nat.factorial (l.count k) := by
  classical
  obtain ⟨L₀, hL₀mem, hL₀parts⟩ := exists_mem_orderedParts_of_shape hP
  obtain ⟨hmap0, hpw0, hun0⟩ := mem_orderedParts.1 hL₀mem
  have hnd0 : L₀.Nodup := nodup_of_mem_orderedParts hL₀mem h0
  have hlen0 : L₀.length = l.length := by rw [← hmap0, List.length_map]
  have hcard_listFun : ∀ (L : List (Finset α)) (h : L.length = l.length),
      L.map Finset.card = l → ∀ i, (listFun L h i).card = listFun l rfl i := by
    intro L h hL i
    simp only [listFun, ← hL, List.getElem_map]
  set f : Fin l.length → ℕ := listFun l rfl with hf
  set g₀ : Fin l.length → Finset α := listFun L₀ hlen0 with hg₀
  have hg₀inj : Function.Injective g₀ := listFun_injective hlen0 hnd0
  have hcg₀ : ∀ i, (g₀ i).card = f i := hcard_listFun L₀ hlen0 hmap0
  set F := (orderedParts s l).filter fun L => L.toFinset = P.parts with hF
  have key : ∀ σ : Equiv.Perm (Fin l.length), f ∘ σ = f → List.ofFn (g₀ ∘ σ) ∈ F := by
    intro σ hσ
    have hperm : (List.ofFn (g₀ ∘ σ)).Perm L₀ := by
      have h := Equiv.Perm.ofFn_comp_perm σ g₀
      rwa [hg₀, ofFn_listFun] at h
    rw [hF, Finset.mem_filter]
    refine ⟨mem_orderedParts.2 ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [List.map_ofFn]
      have hcomp : (Finset.card ∘ (g₀ ∘ ⇑σ)) = f ∘ σ := by
        funext i; simpa using hcg₀ (σ i)
      rw [hcomp, hσ, hf, ofFn_listFun]
    · exact pairwise_disjoint_perm hperm.symm hpw0
    · rw [listUnion_perm hperm]; exact hun0
    · rw [← hL₀parts]
      ext a
      simp only [List.mem_toFinset, hperm.mem_iff]
  have hΦ : Function.Bijective
      (fun σ : {σ : Equiv.Perm (Fin l.length) // f ∘ σ = f} =>
        (⟨List.ofFn (g₀ ∘ σ.1), key σ.1 σ.2⟩ : ↥F)) := by
    constructor
    · rintro ⟨σ, hσ⟩ ⟨τ, hτ⟩ h
      simp only [Subtype.mk.injEq] at h
      have hc := List.ofFn_injective h
      refine Subtype.ext (Equiv.ext fun i => hg₀inj ?_)
      exact congrFun hc i
    · rintro ⟨L, hL⟩
      rw [hF, Finset.mem_filter] at hL
      obtain ⟨hLmem, hLparts⟩ := hL
      obtain ⟨hmapL, hpwL, hunL⟩ := mem_orderedParts.1 hLmem
      have hndL : L.Nodup := nodup_of_mem_orderedParts hLmem h0
      have hlenL : L.length = l.length := by rw [← hmapL, List.length_map]
      set gL : Fin l.length → Finset α := listFun L hlenL with hgL
      have hgLinj : Function.Injective gL := listFun_injective hlenL hndL
      have hcgL : ∀ i, (gL i).card = f i := hcard_listFun L hlenL hmapL
      have hmemL₀ : ∀ i, gL i ∈ L₀ := by
        intro i
        have hmem : gL i ∈ L := by
          rw [hgL]; simp only [listFun]; exact List.getElem_mem _
        rw [← List.mem_toFinset, hLparts, ← hL₀parts, List.mem_toFinset] at hmem
        exact hmem
      have hu : ∀ i, L₀.idxOf (gL i) < l.length := by
        intro i
        rw [← hlen0]
        exact List.idxOf_lt_length_iff.2 (hmemL₀ i)
      have hg₀u : ∀ i, g₀ ⟨L₀.idxOf (gL i), hu i⟩ = gL i := by
        intro i
        rw [hg₀]
        simp only [listFun]
        exact List.getElem_idxOf _
      have huinj : Function.Injective (fun i => (⟨L₀.idxOf (gL i), hu i⟩ : Fin l.length)) := by
        intro i j hij
        apply hgLinj
        rw [← hg₀u i, ← hg₀u j]
        exact congrArg g₀ hij
      refine ⟨⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.1 huinj), ?_⟩, ?_⟩
      · funext i
        change f (Equiv.ofBijective _ (Finite.injective_iff_bijective.1 huinj) i) = f i
        rw [Equiv.ofBijective_apply, ← hcg₀, hg₀u, hcgL]
      · apply Subtype.ext
        change List.ofFn (g₀ ∘ ⇑(Equiv.ofBijective _ (Finite.injective_iff_bijective.1 huinj))) = L
        have hgg : (g₀ ∘ ⇑(Equiv.ofBijective _ (Finite.injective_iff_bijective.1 huinj))) = gL := by
          funext i
          rw [Function.comp_apply, Equiv.ofBijective_apply, hg₀u]
        rw [hgg, hgL, ofFn_listFun]
  have hcardF : Fintype.card {σ : Equiv.Perm (Fin l.length) // f ∘ σ = f} = F.card := by
    rw [← Fintype.card_coe F]
    exact Fintype.card_of_bijective hΦ
  have himg : Finset.image f Finset.univ = l.toFinset := by
    ext k
    simp only [Finset.mem_image, Finset.mem_univ, true_and, List.mem_toFinset]
    constructor
    · rintro ⟨i, rfl⟩
      rw [hf]
      simp only [listFun]
      exact List.getElem_mem _
    · intro hk
      obtain ⟨i, hi, hik⟩ := List.mem_iff_getElem.1 hk
      exact ⟨⟨i, hi⟩, by rw [hf]; exact hik⟩
  have hcnt : ∀ k, Fintype.card {a : Fin l.length // f a = k} = l.count k := by
    intro k
    rw [Fintype.card_subtype]
    have hlc : (l : Multiset ℕ) = Multiset.map f (Finset.univ : Finset (Fin l.length)).val := by
      have h1 : List.ofFn f = l := by rw [hf]; exact ofFn_listFun l rfl
      have h2 : Multiset.map f (Finset.univ : Finset (Fin l.length)).val
          = ↑(List.ofFn f) := by
        rw [List.ofFn_eq_map]
        rfl
      rw [h2, h1]
    rw [← Multiset.coe_count, hlc, Multiset.count_map, Finset.card_def, Finset.filter_val]
    congr 1
    exact Multiset.filter_congr fun a _ => eq_comm
  rw [← hcardF, DomMulAct.stabilizer_card' f, himg]
  exact Finset.prod_congr rfl fun k _ => by rw [hcnt k]

lemma card_orderedParts_eq {s : Finset α} {l : List ℕ} (h0 : (0 : ℕ) ∉ l) :
    (orderedParts s l).card
      = (shapeParts s (l : Multiset ℕ)).card * ∏ k ∈ l.toFinset, Nat.factorial (l.count k) := by
  classical
  have hb : orderedParts s l
      = (shapeParts s (l : Multiset ℕ)).biUnion
          fun P => (orderedParts s l).filter fun L => L.toFinset = P.parts := by
    ext L
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · intro hL
      obtain ⟨P, hPparts, hPshape⟩ := exists_finpartition_of_mem_orderedParts hL h0
      exact ⟨P, mem_shapeParts.2 hPshape, hL, hPparts.symm⟩
    · rintro ⟨P, -, hL, -⟩
      exact hL
  rw [hb, Finset.card_biUnion]
  · rw [Finset.sum_congr rfl (fun P hP => card_fiber_orderedParts (mem_shapeParts.1 hP) h0),
      Finset.sum_const, smul_eq_mul]
  · intro P _ Q _ hPQ
    refine Finset.disjoint_left.2 ?_
    intro L hL hL'
    simp only [Finset.mem_filter] at hL hL'
    exact hPQ (Finpartition.ext (hL.2.symm.trans hL'.2))

/-- **The number of set partitions with prescribed block sizes.**  If `m` is a multiset of
positive integers summing to `|s|`, the set partitions of `s` whose blocks have
cardinalities `m` are counted by `Multiset.bell m`. -/
theorem card_shapeParts (s : Finset α) (m : Multiset ℕ) (h0 : (0 : ℕ) ∉ m)
    (hsum : m.sum = s.card) : (shapeParts s m).card = m.bell := by
  classical
  set l := m.toList with hl
  have hlm : (l : Multiset ℕ) = m := Multiset.coe_toList m
  have h0l : (0 : ℕ) ∉ l := by
    rw [← Multiset.mem_coe, hlm]; exact h0
  have hsum' : l.sum = s.card := by
    rw [← hsum, ← hlm]; rfl
  have key := card_orderedParts_mul_prod_factorial s l hsum'
  rw [card_orderedParts_eq h0l, hlm] at key
  have hprod : ∏ k ∈ l.toFinset, Nat.factorial (l.count k)
      = ∏ j ∈ m.toFinset.erase 0, Nat.factorial (m.count j) := by
    have htf : l.toFinset = m.toFinset := by rw [← hlm]; rfl
    have herase : m.toFinset.erase 0 = m.toFinset :=
      Finset.erase_eq_of_notMem (by simpa using h0)
    rw [htf, herase]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← hlm, Multiset.coe_count]
  have hmapprod : (l.map Nat.factorial).prod = (m.map (fun j => Nat.factorial j)).prod := by
    rw [← hlm]; rfl
  rw [hprod, hmapprod] at key
  have hbell := Multiset.bell_mul_eq m
  rw [← hsum] at key
  have hpos1 : 0 < (m.map (fun j => Nat.factorial j)).prod := by
    refine Multiset.prod_pos fun a ha => ?_
    obtain ⟨b, -, rfl⟩ := Multiset.mem_map.1 ha
    exact Nat.factorial_pos b
  have hpos2 : 0 < ∏ j ∈ m.toFinset.erase 0, Nat.factorial (m.count j) :=
    Finset.prod_pos fun j _ => Nat.factorial_pos _
  have : (shapeParts s m).card * ((∏ j ∈ m.toFinset.erase 0, Nat.factorial (m.count j))
      * (m.map (fun j => Nat.factorial j)).prod)
      = m.bell * ((∏ j ∈ m.toFinset.erase 0, Nat.factorial (m.count j))
      * (m.map (fun j => Nat.factorial j)).prod) := by
    rw [← mul_assoc, ← mul_assoc]
    rw [key]
    rw [← hbell]
    ring
  exact Nat.eq_of_mul_eq_mul_right (by positivity) this

/-- **Partitions into blocks of a fixed size.**  The set partitions of `s` into `a` blocks
of size `n` are counted by `Nat.uniformBell a n`. -/
theorem card_shapeParts_replicate (s : Finset α) (a n : ℕ) (hn : n ≠ 0)
    (hsum : a * n = s.card) :
    (shapeParts s (Multiset.replicate a n)).card = Nat.uniformBell a n := by
  refine card_shapeParts s _ (fun h => hn (Multiset.eq_of_mem_replicate h).symm) ?_
  rw [Multiset.sum_replicate, smul_eq_mul, hsum]

end Finpartition
