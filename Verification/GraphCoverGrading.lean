/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GraphCoverMatrices

/-!
# Graph Cover Grading

Cardinality grading of all concrete graph-cover matrices, including the
actual exterior multiplication defining the contracting homotopy.
-/

namespace Verification.GraphCoverGrading

open Classical
open Verification.GraphCover Verification.GraphCoverFibers
  Verification.GraphCoverCoordinates Verification.GraphCoverCoordinateFacts
  Verification.GraphCoverOrder Verification.GraphCoverBoundaryParts
  Verification.GraphCoverMatrices Verification.EvenGraphBridge
  Verification.GradedPerturbation Verification.GraphSimplexChains

variable {R V : Type*} [CommRing R] [Fintype V] [LinearOrder V]
  (G : SimpleGraph V) (C T : Finset V) (hC : Covers G C)

/-- Cochain indexing of augmented chains: a simplex of cardinality n has degree -n. -/
def degree (J : Simplex G T) : ℤ := -(J.val.card : ℤ)

omit [Fintype V] in
theorem deletion_degree (J : Simplex G T) (i : V) (hi : i ∈ J.val) :
    degree G T (eraseSimplex G T J i) = degree G T J + 1 := by
  have hc := Finset.card_erase_add_one hi
  change -((J.val.erase i).card : ℤ) = -(J.val.card : ℤ) + 1
  omega

theorem outsideMatrix_degree : Homogeneous (degree G T) 1 (outsideMatrix (R := R) G C T) := by
  intro K J h
  rw [outsideMatrix, coefficientMatrix_apply]
  simp only [outsideBoundary, Finsupp.linearCombination_single, one_smul,
    outsideBasis, Finsupp.finset_sum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  have hn : eraseSimplex G T J i ≠ K := by
    intro he
    exact h (he ▸ deletion_degree G T J i (Finset.mem_sdiff.mp hi).1)
  simp [hn]

theorem coverMatrix_degree : Homogeneous (degree G T) 1 (coverMatrix (R := R) G C T) := by
  intro K J h
  rw [coverMatrix, coefficientMatrix_apply]
  simp only [coverBoundary, Finsupp.linearCombination_single, one_smul,
    coverBasis, Finsupp.finset_sum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  have hn : eraseSimplex G T J i ≠ K := by
    intro he
    exact h (he ▸ deletion_degree G T J i (Finset.mem_inter.mp hi).1)
  simp [hn]

theorem word_degree {α : Type*} [Fintype α] [LinearOrder α] (A : Finset α) :
    word (R := R) (A.sort (· ≤ ·)) ∈ ExteriorAlgebra.exteriorPower R A.card (α → R) := by
  rw [← Verification.ExteriorTotalBasis.ofFn_orderEmb, word_ofFn]
  exact ExteriorAlgebra.ιMulti_range R A.card ⟨_,rfl⟩

omit [Fintype V] in
theorem homotopyAt_degree (I : CoverSimplex G C T)
    (A : Finset (RemainingVertex G C T I)) :
    homotopyAt G C T I (word (R := R) (A.sort (· ≤ ·))) ∈
      ExteriorAlgebra.exteriorPower R (A.card+1) (RemainingVertex G C T I → R) := by
  unfold homotopyAt
  split_ifs
  · apply Submodule.smul_mem
    exact Verification.EvenAdmissible.generator_mul_degree _ _ _ (word_degree A)
  · exact Submodule.zero_mem _

theorem contractionMatrix_degree :
    Homogeneous (degree G T) (-1) (contractionMatrix (R := R) G C T hC) := by
  intro K J h
  obtain ⟨⟨I,A⟩,rfl⟩ := (fiberIndexEquiv G C T hC).surjective J
  obtain ⟨⟨L,B⟩,rfl⟩ := (fiberIndexEquiv G C T hC).surjective K
  by_cases he : L = I
  · subst L
    rw [contractionMatrix, fiberMatrix_apply, pureHomotopy_single, Pi.single_eq_same]
    apply Verification.ExteriorTotalBasis.coefficientEquiv_homogeneous (A.card+1)
      ⟨_,homotopyAt_degree G C T I A⟩ B
    intro hb
    apply h
    simp only [degree, fiberIndex_card, Nat.cast_add]
    omega
  · exact contractionMatrix_cover_ne G C T hC ⟨I,A⟩ ⟨L,B⟩ he

#print axioms degree
#print axioms deletion_degree
#print axioms outsideMatrix_degree
#print axioms coverMatrix_degree
#print axioms word_degree
#print axioms homotopyAt_degree
#print axioms contractionMatrix_degree

end Verification.GraphCoverGrading
