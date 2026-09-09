/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.Young.RobinsonSchensted.RecordingStandardization
public import Mathlib.Combinatorics.Young.RobinsonSchensted.Reverse
public import Mathlib.Combinatorics.Young.Word.InverseStandardCat
public import Mathlib.Combinatorics.Young.Word.ShiftedShufflePlactic
public import Mathlib.Data.List.Permutation

/-!
# Free Schur functions as languages, and Littlewood–Richardson triples

A Lean 4 port of the languages `langQ` and of the Littlewood–Richardson–Schützenberger
triples `LRtriple` of `theories/LRrule/shuffle.v` from
[Coq-Combi](https://github.com/math-comp/Coq-Combi).

The *language* of a standard tableau `t` is the set of the words whose recording tableau is
`t`; it is the combinatorial counterpart of the free Schur function indexed by `t`.  Three
standard tableaux `t₁`, `t₂`, `t` form a *Littlewood–Richardson triple* when `t` is the
insertion tableau of some word of the shifted shuffle of two words with insertion tableaux
`t₁` and `t₂`.

The main theorem `List.LRrule_langQ` is the free Littlewood–Richardson rule: the
concatenation of the languages of `t₁` and `t₂` is the union of the languages of the
tableaux `t` making `(t₁, t₂, t)` a Littlewood–Richardson triple.

## Main definitions

* `List.langQ T t` : the words over `T` whose recording tableau is `t` (Coq `langQ`).
* `List.LRtriple t₁ t₂ t` : the Littlewood–Richardson triples (Coq `LRtriple`).

## Main results

* `List.LRtriple_RSQ_append` : concatenating a word of `langQ t₁` and a word of `langQ t₂`
  produces a Littlewood–Richardson triple (Coq `LRtriple_cat_langQ`).
* `List.LRrule_langQ` : **the free Littlewood–Richardson rule** (Coq `LRrule_langQ`).
* `List.LRtriple_cat_equiv` : the same statement in the form of Coq
  `LRtriple_cat_equiv`.
* `List.isStdTab_of_LRtriple` : the third tableau of a Littlewood–Richardson triple is
  standard and has as many boxes as the first two together (Coq
  `is_stdtab_of_n_LRtriple`).
* `List.LRtriple_conjTab` : transposing the three tableaux of a Littlewood–Richardson
  triple gives a Littlewood–Richardson triple (Coq `LRtriple_conj`).
* `List.LRtriple_iff_exists_perm` : a characterisation of the Littlewood–Richardson triples
  by a search over a finite list of words, and the resulting decision procedure
  `List.decidableLRtriple` (Coq `pred_LRtriple` and `LRtripleP`).
-/

@[expose] public section

namespace List

variable {T : Type*} [LinearOrder T]

/-! ### The language of a standard tableau -/

/-- The language of the tableau `t` over the alphabet `T`: the words whose recording
tableau is `t` (Coq `langQ`). -/
def langQ (T : Type*) [LinearOrder T] (t : List (List ℕ)) : Set (List T) := {w | RSQ w = t}

@[simp] lemma mem_langQ {w : List T} {t : List (List ℕ)} : w ∈ langQ T t ↔ RSQ w = t := Iff.rfl

/-- A word belongs to the language of `t` exactly when the insertion tableau of the inverse
of its standardization is `t` (Coq `langQE`). -/
lemma mem_langQ_iff_RS_invStd {w : List T} {t : List (List ℕ)} :
    w ∈ langQ T t ↔ RS (invStd (std w)) = t := by
  rw [mem_langQ, RS_invStd_std]

/-- The words of the language of `t` have as many letters as `t` has boxes
(Coq `size_langQ`). -/
lemma length_eq_sizeTab_of_mem_langQ {w : List T} {t : List (List ℕ)} (h : w ∈ langQ T t) :
    w.length = sizeTab t := by
  rw [mem_langQ] at h
  rw [← h, sizeTab_RSQ]

/-! ### Littlewood–Richardson triples -/

/-- The Littlewood–Richardson–Schützenberger triples: `t` is the insertion tableau of a word
of the shifted shuffle of two words with insertion tableaux `t₁` and `t₂` (Coq
`LRtriple`). -/
def LRtriple (t₁ t₂ t : List (List ℕ)) : Prop :=
  ∃ p₁ p₂ p : List ℕ, RS p₁ = t₁ ∧ RS p₂ = t₂ ∧ RS p = t ∧ p ∈ shsh p₁ p₂

/-- **Concatenating words of two languages produces a Littlewood–Richardson triple** (Coq
`LRtriple_cat_langQ`). -/
theorem LRtriple_RSQ_append {t₁ t₂ : List (List ℕ)} {u₁ u₂ : List T} (h₁ : u₁ ∈ langQ T t₁)
    (h₂ : u₂ ∈ langQ T t₂) : LRtriple t₁ t₂ (RSQ (u₁ ++ u₂)) := by
  refine ⟨invStd (std u₁), invStd (std u₂), invStd (std (u₁ ++ u₂)), ?_, ?_, ?_,
    invStd_std_append_mem_shsh u₁ u₂⟩
  · rw [RS_invStd_std]; exact h₁
  · rw [RS_invStd_std]; exact h₂
  · rw [RS_invStd_std]

/-- A word whose insertion tableau is a standard tableau is a standard word. -/
private lemma isStd_of_isStdTab_RS {p : List ℕ} {t : List (List ℕ)} (ht : IsStdTab t)
    (hp : RS p = t) : IsStd p :=
  (show IsStd (toWord (RS p)) from hp ▸ ht.2).of_perm (perm_toWord_RS p).symm

/-- **The third tableau of a Littlewood–Richardson triple is standard**, with as many boxes
as the first two together (Coq `is_stdtab_of_n_LRtriple`). -/
theorem isStdTab_of_LRtriple {t₁ t₂ t : List (List ℕ)} (ht₁ : IsStdTab t₁) (ht₂ : IsStdTab t₂)
    (h : LRtriple t₁ t₂ t) : IsStdTab t ∧ sizeTab t = sizeTab t₁ + sizeTab t₂ := by
  obtain ⟨p₁, p₂, p, hp₁, hp₂, hp, hsh⟩ := h
  have hs₁ : IsStd p₁ := isStd_of_isStdTab_RS ht₁ hp₁
  have hs₂ : IsStd p₂ := isStd_of_isStdTab_RS ht₂ hp₂
  have hsp : IsStd p := hs₁.of_mem_shsh hs₂ hsh
  refine ⟨hp ▸ isStdTab_RS hsp, ?_⟩
  rw [← hp, sizeTab_RS, length_of_mem_shsh hsh, ← hp₁, ← hp₂, sizeTab_RS, sizeTab_RS]

/-- **Transposing the three tableaux of a Littlewood–Richardson triple gives a
Littlewood–Richardson triple** (Coq `LRtriple_conj`). -/
theorem LRtriple_conjTab {t₁ t₂ t : List (List ℕ)} (ht₁ : IsStdTab t₁) (ht₂ : IsStdTab t₂)
    (h : LRtriple t₁ t₂ t) : LRtriple (conjTab t₁) (conjTab t₂) (conjTab t) := by
  obtain ⟨p₁, p₂, p, hp₁, hp₂, hp, hsh⟩ := h
  have hs₁ : IsStd p₁ := isStd_of_isStdTab_RS ht₁ hp₁
  have hs₂ : IsStd p₂ := isStd_of_isStdTab_RS ht₂ hp₂
  have hsp : IsStd p := hs₁.of_mem_shsh hs₂ hsh
  exact ⟨p₁.reverse, p₂.reverse, p.reverse, by rw [RS_reverse hs₁, hp₁],
    by rw [RS_reverse hs₂, hp₂], by rw [RS_reverse hsp, hp],
    reverse_mem_shsh (fun _ hx => mem_range.1 (hs₁.mem_iff.1 hx)) hsh⟩

/-- **The free Littlewood–Richardson rule** (Coq `LRrule_langQ`): a word splits as a word of
`langQ t₁` followed by a word of `langQ t₂` exactly when it lies in the language of a
tableau `t` forming a Littlewood–Richardson triple with `t₁` and `t₂`. -/
theorem LRrule_langQ {t₁ t₂ : List (List ℕ)} (ht₁ : IsStdTab t₁) (w : List T) :
    (∃ u v, w = u ++ v ∧ u ∈ langQ T t₁ ∧ v ∈ langQ T t₂) ↔
      ∃ t, LRtriple t₁ t₂ t ∧ w ∈ langQ T t := by
  constructor
  · rintro ⟨u, v, rfl, hu, hv⟩
    exact ⟨RSQ (u ++ v), LRtriple_RSQ_append hu hv, rfl⟩
  · rintro ⟨t, ⟨p₁, p₂, p, hp₁, hp₂, hp, hsh⟩, hw⟩
    have hstd₁ : IsStd p₁ := isStd_of_isStdTab_RS ht₁ hp₁
    have hpl : PlacticEquiv (invStd (std w)) p :=
      placticEquiv_iff_RS_eq.2 (by rw [RS_invStd_std, mem_langQ.1 hw, ← hp])
    obtain ⟨hf, hs⟩ := hstd₁.mem_shsh.1 hsh
    have hlenw : w.length = p.length := by simpa using hpl.perm.length_eq
    have hn : p₁.length ≤ w.length := by
      have := length_of_mem_shsh hsh
      omega
    set n := p₁.length
    refine ⟨w.take n, w.drop n, (List.take_append_drop _ _).symm, ?_, ?_⟩
    · rw [mem_langQ_iff_RS_invStd, ← filter_lt_invStd_std_take hn, ← hp₁, ← hf]
      refine RS_eq_of_placticEquiv ?_
      simpa only [ltFilter] using placticEquiv_ltFilter (N := n) hpl
    · rw [mem_langQ_iff_RS_invStd, ← sfilterleq_invStd_std_drop hn, ← hp₂, ← hs]
      exact RS_eq_of_placticEquiv (placticEquiv_sfilterleq _ hpl)

/-- **The free Littlewood–Richardson rule, in the form of Coq `LRtriple_cat_equiv`**: two
words lie in the languages of `t₁` and `t₂` exactly when they have the right lengths and
their concatenation lies in the language of a tableau forming a Littlewood–Richardson
triple with `t₁` and `t₂`. -/
theorem LRtriple_cat_equiv {t₁ t₂ : List (List ℕ)} (ht₁ : IsStdTab t₁) (u₁ u₂ : List T) :
    (u₁ ∈ langQ T t₁ ∧ u₂ ∈ langQ T t₂) ↔
      (u₁.length = sizeTab t₁ ∧ u₂.length = sizeTab t₂ ∧
        ∃ t, LRtriple t₁ t₂ t ∧ u₁ ++ u₂ ∈ langQ T t) := by
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨length_eq_sizeTab_of_mem_langQ h₁, length_eq_sizeTab_of_mem_langQ h₂,
      RSQ (u₁ ++ u₂), LRtriple_RSQ_append h₁ h₂, rfl⟩
  · rintro ⟨hl₁, -, t, ⟨p₁, p₂, p, hp₁, hp₂, hp, hsh⟩, hw⟩
    have hstd₁ : IsStd p₁ := isStd_of_isStdTab_RS ht₁ hp₁
    have hlen₁ : p₁.length = u₁.length := by
      rw [← sizeTab_RS p₁, hp₁, hl₁]
    have hpl : PlacticEquiv (invStd (std (u₁ ++ u₂))) p :=
      placticEquiv_iff_RS_eq.2 (by rw [RS_invStd_std, mem_langQ.1 hw, ← hp])
    obtain ⟨hf, hs⟩ := hstd₁.mem_shsh.1 hsh
    rw [hlen₁] at hf hs
    constructor
    · rw [mem_langQ_iff_RS_invStd, ← filter_lt_invStd_std_append u₁ u₂, ← hp₁, ← hf]
      refine RS_eq_of_placticEquiv ?_
      simpa only [ltFilter] using placticEquiv_ltFilter (N := u₁.length) hpl
    · rw [mem_langQ_iff_RS_invStd, ← sfilterleq_invStd_std_append u₁ u₂, ← hp₂, ← hs]
      exact RS_eq_of_placticEquiv (placticEquiv_sfilterleq _ hpl)

/-! ### A finite characterisation of the Littlewood–Richardson triples -/

/-- Every standard tableau is the recording tableau of a standard word. -/
theorem exists_isStd_RSQ_eq {t : List (List ℕ)} (ht : IsStdTab t) :
    ∃ w : List ℕ, IsStd w ∧ RSQ w = t := by
  obtain ⟨w, hRS, hRSQ⟩ := exists_word_RS_RSQ (T := ℕ) ht.1 ht rfl
  exact ⟨w, isStd_of_isStdTab_RS ht hRS, hRSQ⟩

/-- **The Littlewood–Richardson triples are characterised by a search over the permutations
of `range (sizeTab t₁ + sizeTab t₂)`**: `(t₁, t₂, t)` is a triple exactly when some standard
word of that length has `t₁`, `t₂` and `t` as the recording tableaux of its prefix of length
`sizeTab t₁`, of the corresponding suffix, and of itself.  It plays the role of the
executable predicate `pred_LRtriple` of Coq-Combi, with a search over the permutations of
`range (sizeTab t₁ + sizeTab t₂)` in place of the search over a shifted shuffle. -/
theorem LRtriple_iff_exists_perm {t₁ t₂ t : List (List ℕ)} (ht₁ : IsStdTab t₁)
    (ht₂ : IsStdTab t₂) :
    LRtriple t₁ t₂ t ↔
      ∃ w ∈ (List.range (sizeTab t₁ + sizeTab t₂)).permutations,
        RSQ (w.take (sizeTab t₁)) = t₁ ∧ RSQ (w.drop (sizeTab t₁)) = t₂ ∧ RSQ w = t := by
  constructor
  · intro h
    obtain ⟨htstd, hsize⟩ := isStdTab_of_LRtriple ht₁ ht₂ h
    obtain ⟨w, hwstd, hw⟩ := exists_isStd_RSQ_eq htstd
    have hlen : w.length = sizeTab t :=
      length_eq_sizeTab_of_mem_langQ (T := ℕ) (mem_langQ.2 hw)
    obtain ⟨u, v, huv, hu, hv⟩ := (LRrule_langQ ht₁ w).2 ⟨t, h, mem_langQ.2 hw⟩
    have hulen : u.length = sizeTab t₁ := length_eq_sizeTab_of_mem_langQ hu
    have htk : w.take (sizeTab t₁) = u := by rw [huv]; exact List.take_left' hulen
    have hdr : w.drop (sizeTab t₁) = v := by rw [huv]; exact List.drop_left' hulen
    exact ⟨w, List.mem_permutations.2 (by rw [← hsize, ← hlen]; exact hwstd),
      htk ▸ hu, hdr ▸ hv, hw⟩
  · rintro ⟨w, -, hu, hv, hw⟩
    have h := LRtriple_RSQ_append (T := ℕ) (mem_langQ.2 hu) (mem_langQ.2 hv)
    rwa [List.take_append_drop, hw] at h

/-- **Being a Littlewood–Richardson triple is decidable** (Coq `LRtripleP`). -/
def decidableLRtriple {t₁ t₂ t : List (List ℕ)} (ht₁ : IsStdTab t₁) (ht₂ : IsStdTab t₂) :
    Decidable (LRtriple t₁ t₂ t) :=
  decidable_of_iff _ (LRtriple_iff_exists_perm ht₁ ht₂).symm

end List
