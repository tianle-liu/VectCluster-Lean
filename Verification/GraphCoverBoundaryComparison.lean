/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GraphCoverCoordinateFacts
import Verification.GraphCoverBoundaryParts

/-!
# Graph Cover Boundary Comparison

The outside-vertex component of the literal graph boundary equals the explicit
exterior fiber boundary, including its cover-first orientation sign.
-/

namespace Verification.GraphCoverBoundaryComparison

open Verification.GraphCover Verification.GraphCoverFibers
  Verification.GraphCoverCoordinates Verification.GraphCoverCoordinateFacts
  Verification.GraphCoverOrder Verification.GraphCoverBoundaryParts
  Verification.EvenDifferential Verification.EvenGraphBridge

variable {R V : Type*} [CommRing R] [Fintype V] [LinearOrder V]
  (G : SimpleGraph V) (C T : Finset V) (hC : Covers G C)

omit [Fintype V] in
open Classical in
theorem pureBoundary_single (I : CoverSimplex G C T)
    (x : FiberExterior (R := R) G C T I) :
    pureBoundary G C T (Pi.single I x) = Pi.single I (boundaryAt G C T I x) := by
  classical
  funext J
  by_cases h : J = I
  · subst J
    simp [pureBoundary]
  · simp [pureBoundary, h]

/-- Coordinate computation of the already constructed pure contraction boundary. -/
theorem coordinate_pure_boundary_single (I : CoverSimplex G C T)
    (A : Finset (RemainingVertex G C T I)) :
    coefficientEquiv G C T hC (pureBoundary G C T
      ((coefficientEquiv (R := R) G C T hC).symm
        (Finsupp.single (fiberIndexEquiv G C T hC ⟨I,A⟩) 1))) =
    ∑ a ∈ A, Finsupp.single (fiberIndexEquiv G C T hC ⟨I,A.erase a⟩)
      (phase (R := R) G C T I * (-1)^rankBelow A a) := by
  classical
  rw [coefficientEquiv_symm_single, one_smul, pureBoundary_single]
  simp only [boundaryAt, LinearMap.smul_apply,
    Verification.AugmentedSimplexContraction.boundary_word, Finset.smul_sum, smul_smul]
  change coefficientEquiv G C T hC
    (LinearMap.single R (fun I => FiberExterior (R := R) G C T I) I
      (∑ a ∈ A, (phase (R := R) G C T I * (-1)^rankBelow A a) •
        word ((A.erase a).sort (· ≤ ·)))) = _
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact coefficientEquiv_single_word G C T hC ⟨I,A.erase a⟩ _

omit [Fintype V] in
/-- The same matrix entries computed directly by graph simplex deletion. -/
theorem outsideBasis_fiber (hord : CoverOrdered C) (I : CoverSimplex G C T)
    (A : Finset (RemainingVertex G C T I)) :
    outsideBasis (R := R) G C T (fiberIndexEquiv G C T hC ⟨I,A⟩) =
      ∑ a ∈ A, Finsupp.single (fiberIndexEquiv G C T hC ⟨I,A.erase a⟩)
        (phase (R := R) G C T I * (-1)^rankBelow A a) := by
  rw [outsideBasis, fiberIndex_outside, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro a _
  change Finsupp.single (Verification.GraphSimplexChains.eraseSimplex G T
    (fiberIndexEquiv G C T hC ⟨I,A⟩) a.val)
    ((-1 : R)^rankBelow (fiberIndexEquiv G C T hC ⟨I,A⟩).val a.val) = _
  rw [fiberIndex_erase_outside, fiberIndex_outside_rank G C T hC hord, pow_add]
  rfl

/-- Literal global boundary comparison. It is proved on the independent-simplex basis,
with no assumed conjugacy or cancellation identity. -/
theorem outside_conjugacy (hord : CoverOrdered C) :
    (coefficientEquiv (R := R) G C T hC).conjRingEquiv (pureBoundary G C T) =
      outsideBoundary G C T := by
  apply Finsupp.lhom_ext
  intro J r
  obtain ⟨⟨I,A⟩,rfl⟩ := (fiberIndexEquiv G C T hC).surjective J
  have hs : Finsupp.single (fiberIndexEquiv G C T hC ⟨I,A⟩) r =
      r • Finsupp.single (fiberIndexEquiv G C T hC ⟨I,A⟩) (1 : R) := by simp
  rw [hs, map_smul, map_smul]
  change r • coefficientEquiv G C T hC (pureBoundary G C T
      ((coefficientEquiv (R := R) G C T hC).symm
        (Finsupp.single (fiberIndexEquiv G C T hC ⟨I,A⟩) 1))) = _
  rw [coordinate_pure_boundary_single, ← outsideBasis_fiber G C T hC hord]
  simp only [outsideBoundary, Finsupp.linearCombination_single, one_smul]

#print axioms pureBoundary_single
#print axioms coordinate_pure_boundary_single
#print axioms outsideBasis_fiber
#print axioms outside_conjugacy

end Verification.GraphCoverBoundaryComparison
