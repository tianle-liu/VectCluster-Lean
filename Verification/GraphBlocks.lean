/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Finsupp.SumProd
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Lean.Elab.Tactic.Omega

/-!
# Graph Blocks

The original finite block decomposition of the even Witt complex in
manuscript.tex, proof of `thm:even-graph-CW` (lines 2294–2334).

This file defines the monomial and induced-independent-set basis indices,
their actual equivalence, and the corresponding free-module maps. The
coefficient ring is arbitrary. No geometric Witt comparison is assumed.
-/

namespace Verification.GraphBlocks

open Finset

variable {V C : Type*} [DecidableEq V] [DecidableEq C]

/-- Vertices of the induced complex in the block `(S,F)`. -/
def available (c : V → C) (S : Finset V) (F : Finset C) : Finset V :=
  S.filter fun i => c i ∉ F

/-- Original torus-monomial index `(I,A,F)`. -/
structure MonomialIndex (G : SimpleGraph V) (c : V → C) where
  I : Finset V
  A : Finset V
  F : Finset C
  independent : G.IsIndepSet (I : Set V)
  disjoint : Disjoint I A
  avoids : Disjoint (I.image c) F

/-- A simplex of the induced independence complex in the block `(S,F)`. -/
structure BlockIndex (G : SimpleGraph V) (c : V → C) where
  S : Finset V
  F : Finset C
  I : Finset V
  independent : G.IsIndepSet (I : Set V)
  subset : I ⊆ available c S F

variable {G : SimpleGraph V} {c : V → C}

omit [DecidableEq V] in
@[ext] theorem MonomialIndex.ext {x y : MonomialIndex G c}
    (hI : x.I = y.I) (hA : x.A = y.A) (hF : x.F = y.F) : x = y := by
  cases x
  cases y
  simp_all

omit [DecidableEq V] in
@[ext] theorem BlockIndex.ext {x y : BlockIndex G c}
    (hS : x.S = y.S) (hF : x.F = y.F) (hI : x.I = y.I) : x = y := by
  cases x
  cases y
  simp_all

def toBlock (x : MonomialIndex G c) : BlockIndex G c where
  S := x.I ∪ x.A
  F := x.F
  I := x.I
  independent := x.independent
  subset := by
    intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_union_left _ hi, ?_⟩
    exact fun hF => (Finset.disjoint_left.mp x.avoids)
      (Finset.mem_image.mpr ⟨i, hi, rfl⟩) hF

def fromBlock (b : BlockIndex G c) : MonomialIndex G c where
  I := b.I
  A := b.S \ b.I
  F := b.F
  independent := b.independent
  disjoint := by
    apply Finset.disjoint_left.mpr
    intro i hi hA
    exact (Finset.mem_sdiff.mp hA).2 hi
  avoids := by
    apply Finset.disjoint_left.mpr
    intro a ha hF
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact (Finset.mem_filter.mp (b.subset hi)).2 hF

theorem fromBlock_toBlock (x : MonomialIndex G c) : fromBlock (toBlock x) = x := by
  apply MonomialIndex.ext
  · rfl
  · change (x.I ∪ x.A) \ x.I = x.A
    ext i
    constructor
    · intro h
      have h' := Finset.mem_sdiff.mp h
      exact (Finset.mem_union.mp h'.1).resolve_left h'.2
    · intro hi
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hi,
        fun hI => (Finset.disjoint_left.mp x.disjoint) hI hi⟩
  · rfl

theorem toBlock_fromBlock (b : BlockIndex G c) : toBlock (fromBlock b) = b := by
  apply BlockIndex.ext
  · change b.I ∪ (b.S \ b.I) = b.S
    ext i
    constructor
    · intro hi
      rcases Finset.mem_union.mp hi with hI | hA
      · exact (Finset.mem_filter.mp (b.subset hI)).1
      · exact (Finset.mem_sdiff.mp hA).1
    · intro hi
      by_cases hI : i ∈ b.I
      · exact Finset.mem_union_left _ hI
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hi, hI⟩)
  · rfl
  · rfl

/-- The precise monomial-to-simplex basis bijection. -/
def indexEquiv (G : SimpleGraph V) (c : V → C) : MonomialIndex G c ≃ BlockIndex G c where
  toFun := toBlock
  invFun := fromBlock
  left_inv := fromBlock_toBlock
  right_inv := toBlock_fromBlock

theorem indexEquiv_preserves_degree (x : MonomialIndex G c) :
    (indexEquiv G c x).I.card = x.I.card := rfl

/-- The admissible contractions of the original monomial basis. -/
def CanAdd (x : MonomialIndex G c) (i : V) : Prop :=
  i ∈ x.A ∧ c i ∉ x.F ∧ G.IsIndepSet ((insert i x.I : Finset V) : Set V)

/-- The admissible cofaces in the induced independence complex. -/
def CanAddBlock (b : BlockIndex G c) (i : V) : Prop :=
  i ∈ available c b.S b.F ∧ i ∉ b.I ∧
    G.IsIndepSet ((insert i b.I : Finset V) : Set V)

theorem canAdd_iff (x : MonomialIndex G c) (i : V) :
    CanAdd x i ↔ CanAddBlock (toBlock x) i := by
  constructor
  · rintro ⟨hA, hF, hind⟩
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_union_right _ hA, hF⟩, ?_, hind⟩
    exact fun hI => (Finset.disjoint_left.mp x.disjoint) hI hA
  · rintro ⟨hi, hI, hind⟩
    have h := Finset.mem_filter.mp hi
    exact ⟨(Finset.mem_union.mp h.1).resolve_left hI, h.2, hind⟩

def addMonomial (x : MonomialIndex G c) (i : V) (h : CanAdd x i) :
    MonomialIndex G c where
  I := insert i x.I
  A := x.A.erase i
  F := x.F
  independent := h.2.2
  disjoint := by
    apply Finset.disjoint_left.mpr
    intro j hj hA
    have hA' := Finset.mem_erase.mp hA
    rcases Finset.mem_insert.mp hj with hji | hjI
    · exact hA'.1 hji
    · exact (Finset.disjoint_left.mp x.disjoint) hjI hA'.2
  avoids := by
    simpa only [Finset.image_insert, Finset.disjoint_insert_left] using ⟨h.2.1, x.avoids⟩

def addBlock (b : BlockIndex G c) (i : V) (h : CanAddBlock b i) : BlockIndex G c where
  S := b.S
  F := b.F
  I := insert i b.I
  independent := h.2.2
  subset := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact h.1
    · exact b.subset hj

theorem toBlock_addMonomial (x : MonomialIndex G c) (i : V) (h : CanAdd x i) :
    toBlock (addMonomial x i h) = addBlock (toBlock x) i ((canAdd_iff x i).mp h) := by
  apply BlockIndex.ext
  · change insert i x.I ∪ x.A.erase i = x.I ∪ x.A
    ext j
    by_cases hji : j = i
    · subst j
      simp [h.1]
    · simp [hji]
  · rfl
  · rfl

theorem addMonomial_degree (x : MonomialIndex G c) (i : V) (h : CanAdd x i) :
    (addMonomial x i h).I.card = x.I.card + 1 := by
  apply Finset.card_insert_of_not_mem
  exact fun hi => (Finset.disjoint_left.mp x.disjoint) hi h.1

/-- All simplices, including the empty simplex, of the induced independence complex. -/
abbrev SimplexIndex (G : SimpleGraph V) (c : V → C) (SF : Finset V × Finset C) :=
  {I : Finset V // G.IsIndepSet (I : Set V) ∧ I ⊆ available c SF.1 SF.2}

/-- Separating the block label from its simplex index. -/
def blockSigmaEquiv (G : SimpleGraph V) (c : V → C) :
    BlockIndex G c ≃ Σ SF : Finset V × Finset C, SimplexIndex G c SF where
  toFun b := ⟨(b.S, b.F), ⟨b.I, b.independent, b.subset⟩⟩
  invFun b := ⟨b.1.1, b.1.2, b.2.1, b.2.2.1, b.2.2.2⟩
  left_inv b := by cases b; rfl
  right_inv b := by rcases b with ⟨⟨S,F⟩,⟨I,hi,hsub⟩⟩; rfl

variable (R : Type*) [CommRing R]

/-- The induced equivalence of actual free coefficient modules. -/
noncomputable def coefficientEquiv (G : SimpleGraph V) (c : V → C) :
    (MonomialIndex G c →₀ R) ≃ₗ[R] (BlockIndex G c →₀ R) :=
  Finsupp.domLCongr (indexEquiv G c)

theorem coefficientEquiv_single (x : MonomialIndex G c) (a : R) :
    coefficientEquiv R G c (Finsupp.single x a) = Finsupp.single (toBlock x) a := by
  exact Finsupp.domLCongr_single _ _ _

/-- The actual finite direct product of the induced-simplex coefficient modules. -/
noncomputable def coefficientBlocksEquiv [Fintype V] [Fintype C]
    (G : SimpleGraph V) (c : V → C) :
    (MonomialIndex G c →₀ R) ≃ₗ[R]
      ((SF : Finset V × Finset C) → (SimplexIndex G c SF →₀ R)) :=
  ((coefficientEquiv R G c).trans (Finsupp.domLCongr (blockSigmaEquiv G c))).trans
    (Finsupp.sigmaFinsuppLEquivPiFinsupp R)

section Differential

variable [Fintype V] [LinearOrder V]

/-- The increasing-vertex incidence coefficient at the coface adding `i`. -/
def incidence (I : Finset V) (i : V) : R := (-1 : R) ^ (I.filter (· < i)).card

/-- Original contraction differential, independently defined on monomials. -/
noncomputable def monomialBasisDifferential (x : MonomialIndex G c) :
    MonomialIndex G c →₀ R := by
  classical
  exact ∑ i : V, if h : CanAdd x i then
    Finsupp.single (addMonomial x i h) (incidence R x.I i) else 0

/-- Augmented simplicial incidence in each induced-independent-set block. -/
noncomputable def blockBasisDifferential (b : BlockIndex G c) : BlockIndex G c →₀ R := by
  classical
  exact ∑ i : V, if h : CanAddBlock b i then
    Finsupp.single (addBlock b i h) (incidence R b.I i) else 0

noncomputable def monomialDifferential :
    (MonomialIndex G c →₀ R) →ₗ[R] (MonomialIndex G c →₀ R) :=
  Finsupp.linearCombination R (monomialBasisDifferential R)

noncomputable def blockDifferential :
    (BlockIndex G c →₀ R) →ₗ[R] (BlockIndex G c →₀ R) :=
  Finsupp.linearCombination R (blockBasisDifferential R)

/-- Basis transport takes each contraction, with its sign, to the simplicial coface. -/
theorem transport_basis_differential (x : MonomialIndex G c) :
    coefficientEquiv R G c (monomialBasisDifferential R x) =
      blockBasisDifferential R (toBlock x) := by
  classical
  unfold monomialBasisDifferential blockBasisDifferential
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : CanAdd x i
  · have hb := (canAdd_iff x i).mp h
    rw [dif_pos h, dif_pos hb, coefficientEquiv_single, toBlock_addMonomial]
    rfl
  · have hb : ¬CanAddBlock (toBlock x) i := fun hb => h ((canAdd_iff x i).mpr hb)
    simp only [dif_neg h, dif_neg hb, map_zero]

/-- Equality of actual linear maps: the reindexing intertwines the differentials. -/
theorem coefficient_differential_commutes :
    (coefficientEquiv R G c).toLinearMap.comp (monomialDifferential (G := G) (c := c) R) =
      (blockDifferential (G := G) (c := c) R).comp (coefficientEquiv R G c).toLinearMap := by
  apply Finsupp.lhom_ext
  intro x a
  change coefficientEquiv R G c (monomialDifferential R (Finsupp.single x a)) =
    blockDifferential R (coefficientEquiv R G c (Finsupp.single x a))
  simp only [monomialDifferential, blockDifferential, Finsupp.linearCombination_single,
    map_smul, coefficientEquiv_single, transport_basis_differential]

/-- Conjugating the original differential gives the block incidence differential. -/
theorem differential_conjugation :
    (coefficientEquiv R G c).toLinearMap.comp
      ((monomialDifferential (G := G) (c := c) R).comp
        (coefficientEquiv R G c).symm.toLinearMap) =
      blockDifferential (G := G) (c := c) R := by
  rw [← LinearMap.comp_assoc, coefficient_differential_commutes, LinearMap.comp_assoc]
  ext b
  simp

omit [Fintype V] [LinearOrder V] in
/-- Every simplicial coface stays in exactly the same `(S,F)` block. -/
theorem addBlock_preserves_label (b : BlockIndex G c) (i : V) (h : CanAddBlock b i) :
    (addBlock b i h).S = b.S ∧ (addBlock b i h).F = b.F := ⟨rfl, rfl⟩

end Differential

section Multiplicity

variable [Fintype V]

/-- The union of the coefficient color classes indexed by `F`. -/
def colorPreimage (c : V → C) (F : Finset C) : Finset V :=
  Finset.univ.filter fun i => c i ∈ F

omit [DecidableEq V] in
theorem colorPreimage_card (c : V → C) (F : Finset C) :
    (colorPreimage c F).card =
      ∑ a ∈ F, (Finset.univ.filter fun i : V => c i = a).card :=
  (Finset.sum_card_fiberwise_eq_card_filter Finset.univ F c).symm

omit [DecidableEq V] in
/-- The paper's powerset sum is exactly the product over missing colors. -/
theorem multiplicity_product (c : V → C) (D : Finset C) :
    (∑ F ∈ D.powerset, 2 ^ (colorPreimage c F).card) =
      ∏ a ∈ D, (1 + 2 ^ (Finset.univ.filter fun i : V => c i = a).card) := by
  rw [Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro F _
  rw [colorPreimage_card, Finset.prod_pow_eq_pow_sum]

omit [DecidableEq V] in
theorem disjoint_colorPreimage (T : Finset V) (F : Finset C)
    (h : Disjoint (T.image c) F) : Disjoint T (colorPreimage c F) := by
  apply Finset.disjoint_left.mpr
  intro i hi hp
  exact (Finset.disjoint_left.mp h) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    (Finset.mem_filter.mp hp).2

theorem available_union_extra (T A : Finset V) (F : Finset C)
    (hT : Disjoint (T.image c) F) (hA : A ⊆ colorPreimage c F) :
    available c (T ∪ A) F = T := by
  ext i
  constructor
  · intro hi
    have h := Finset.mem_filter.mp hi
    rcases Finset.mem_union.mp h.1 with hT | hAi
    · exact hT
    · exact False.elim (h.2 (Finset.mem_filter.mp (hA hAi)).2)
  · intro hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hi, ?_⟩
    exact fun hF => (Finset.disjoint_left.mp hT)
      (Finset.mem_image.mpr ⟨i, hi, rfl⟩) hF

theorem recover_block_set (S T : Finset V) (F : Finset C)
    (h : available c S F = T) : T ∪ (S ∩ colorPreimage c F) = S := by
  rw [← h]
  ext i
  simp only [Finset.mem_union, available, colorPreimage,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
  by_cases hi : c i ∈ F <;> simp [hi]

/-- For each allowable frozen subset, extra vertices are freely chosen in its color classes. -/
def fixedFrozenEquiv (T : Finset V) (F : Finset C) (hT : Disjoint (T.image c) F) :
    {S : Finset V // available c S F = T} ≃
      {A : Finset V // A ⊆ colorPreimage c F} where
  toFun S := ⟨S.val ∩ colorPreimage c F, Finset.inter_subset_right⟩
  invFun A := ⟨T ∪ A.val, available_union_extra T A.val F hT A.property⟩
  left_inv S := Subtype.ext (recover_block_set S.val T F S.property)
  right_inv A := by
    apply Subtype.ext
    ext i
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨h, hp⟩
      exact h.resolve_left (fun hi => (Finset.disjoint_left.mp
        (disjoint_colorPreimage T F hT)) hi hp)
    · intro hi
      exact ⟨Or.inr hi, A.property hi⟩

theorem fixedFrozen_count (T : Finset V) (F : Finset C)
    (hT : Disjoint (T.image c) F) :
    Fintype.card {S : Finset V // available c S F = T} = 2 ^ (colorPreimage c F).card := by
  rw [Fintype.card_congr (fixedFrozenEquiv T F hT)]
  have e : {A : Finset V // A ⊆ colorPreimage c F} ≃
      ↥((colorPreimage c F).powerset) :=
    Equiv.subtypeEquivRight fun _ => Finset.mem_powerset.symm
  rw [Fintype.card_congr e, Fintype.card_coe, Finset.card_powerset]

theorem principal_coefficient_weight (T : Finset V) :
    (∏ a ∈ Finset.univ \ T,
      (1 + 2 ^ (Finset.univ.filter fun i : V => i = a).card)) =
      3 ^ (Fintype.card V - T.card) := by
  have hf (a : V) : (Finset.univ.filter fun i : V => i = a) = {a} := by
    ext i
    simp
  simp_rw [hf, Finset.card_singleton]
  change (∏ _a ∈ Finset.univ \ T, (3 : ℕ)) = 3 ^ (Fintype.card V - T.card)
  rw [Finset.prod_const, Finset.card_sdiff (Finset.subset_univ T), Finset.card_univ]

end Multiplicity

#print axioms MonomialIndex.ext
#print axioms BlockIndex.ext
#print axioms fromBlock_toBlock
#print axioms toBlock_fromBlock
#print axioms indexEquiv
#print axioms indexEquiv_preserves_degree
#print axioms canAdd_iff
#print axioms toBlock_addMonomial
#print axioms addMonomial_degree
#print axioms coefficientEquiv
#print axioms coefficientEquiv_single
#print axioms blockSigmaEquiv
#print axioms coefficientBlocksEquiv
#print axioms monomialBasisDifferential
#print axioms blockBasisDifferential
#print axioms monomialDifferential
#print axioms blockDifferential
#print axioms transport_basis_differential
#print axioms coefficient_differential_commutes
#print axioms differential_conjugation
#print axioms addBlock_preserves_label
#print axioms colorPreimage_card
#print axioms multiplicity_product
#print axioms disjoint_colorPreimage
#print axioms available_union_extra
#print axioms recover_block_set
#print axioms fixedFrozenEquiv
#print axioms fixedFrozen_count
#print axioms principal_coefficient_weight
#print axioms available
#print axioms toBlock
#print axioms fromBlock
#print axioms CanAdd
#print axioms CanAddBlock
#print axioms addMonomial
#print axioms addBlock
#print axioms incidence
#print axioms colorPreimage

end Verification.GraphBlocks

-- Explicit dependency audit of the early module constructions.
#print axioms Verification.GraphBlocks.BlockIndex
#print axioms Verification.GraphBlocks.MonomialIndex
#print axioms Verification.GraphBlocks.SimplexIndex
