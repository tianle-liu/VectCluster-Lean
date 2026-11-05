/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GraphSimplexChains
import Verification.GraphCoverOrder

/-!
# Graph Cover Boundary Parts

Literal separation of the graph boundary into outside and cover deletions.
Cover deletion strictly raises the complementary cover-cardinality filtration.
-/

namespace Verification.GraphCoverBoundaryParts

open Verification.GraphCover Verification.GraphSimplexChains Verification.EvenDifferential

variable {R V : Type*} [CommRing R] [LinearOrder V]
  (G : SimpleGraph V) (C T : Finset V)

noncomputable def outsideBasis (J : Simplex G T) : Simplex G T →₀ R :=
  ∑ i ∈ J.val \ C, Finsupp.single (eraseSimplex G T J i) ((-1 : R)^rankBelow J.val i)

noncomputable def coverBasis (J : Simplex G T) : Simplex G T →₀ R :=
  ∑ i ∈ J.val ∩ C, Finsupp.single (eraseSimplex G T J i) ((-1 : R)^rankBelow J.val i)

noncomputable def outsideBoundary : (Simplex G T →₀ R) →ₗ[R] (Simplex G T →₀ R) :=
  Finsupp.linearCombination R (outsideBasis G C T)

noncomputable def coverBoundary : (Simplex G T →₀ R) →ₗ[R] (Simplex G T →₀ R) :=
  Finsupp.linearCombination R (coverBasis G C T)

theorem basisBoundary_split (J : Simplex G T) :
    basisBoundary (R := R) G T J = outsideBasis G C T J + coverBasis G C T J := by
  rw [outsideBasis, coverBasis, add_comm]
  exact (Finset.sum_inter_add_sum_diff J.val C _).symm

theorem boundary_split :
    boundary (R := R) G T = outsideBoundary G C T + coverBoundary G C T := by
  apply Finsupp.lhom_ext
  intro J r
  simp only [boundary, outsideBoundary, coverBoundary, LinearMap.add_apply,
    Finsupp.linearCombination_single]
  rw [basisBoundary_split G C T J, smul_add]

/-- Reverse cover cardinality makes chain deletion a strictly increasing filtration. -/
def weight (J : Simplex G T) : ℕ := C.card - (J.val ∩ C).card

theorem weight_bound (J : Simplex G T) : weight G C T J ≤ C.card := Nat.sub_le _ _

theorem erase_inter (J C : Finset V) (i : V) : (J.erase i) ∩ C = (J ∩ C).erase i := by
  ext v
  simp only [Finset.mem_inter, Finset.mem_erase]
  tauto

theorem weight_erase_cover (J : Simplex G T) (i : V) (hi : i ∈ J.val ∩ C) :
    weight G C T (eraseSimplex G T J i) = weight G C T J + 1 := by
  have hc := Finset.card_le_card (Finset.inter_subset_right (s₁ := J.val) (s₂ := C))
  have he := Finset.card_erase_add_one hi
  change C.card - (J.val.erase i ∩ C).card = C.card - (J.val ∩ C).card + 1
  rw [erase_inter]
  omega

theorem weight_erase_outside (J : Simplex G T) (i : V) (hi : i ∉ C) :
    weight G C T (eraseSimplex G T J i) = weight G C T J := by
  change C.card - (J.val.erase i ∩ C).card = _
  rw [erase_inter, Finset.erase_eq_of_not_mem (by simp [hi])]
  rfl

theorem coverBasis_raises (J K : Simplex G T) (h : weight G C T K ≤ weight G C T J) :
    coverBasis (R := R) G C T J K = 0 := by
  classical
  simp only [coverBasis, Finsupp.finset_sum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  have hn : eraseSimplex G T J i ≠ K := by
    intro he
    have hw := weight_erase_cover G C T J i hi
    rw [he] at hw
    omega
  simp [hn]

theorem outsideBasis_preserves_weight (J K : Simplex G T)
    (h : weight G C T K ≠ weight G C T J) :
    outsideBasis (R := R) G C T J K = 0 := by
  classical
  simp only [outsideBasis, Finsupp.finset_sum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  have hn : eraseSimplex G T J i ≠ K := by
    intro he
    exact h (he ▸ weight_erase_outside G C T J i (Finset.mem_sdiff.mp hi).2)
  simp [hn]

#print axioms outsideBasis
#print axioms coverBasis
#print axioms outsideBoundary
#print axioms coverBoundary
#print axioms basisBoundary_split
#print axioms boundary_split
#print axioms weight
#print axioms weight_bound
#print axioms erase_inter
#print axioms weight_erase_cover
#print axioms weight_erase_outside
#print axioms coverBasis_raises
#print axioms outsideBasis_preserves_weight

end Verification.GraphCoverBoundaryParts
