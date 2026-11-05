/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GraphCoverBoundaryComparison
import Verification.PerturbedHomologyModel

/-!
# Graph Cover Matrices

Concrete finite matrices for the graph-cover cancellation. The graph boundary
is independently defined by deletion. Its outside part is identified with the
explicit simplex-fiber contraction, and the cover part strictly raises a finite
filtration. No nilpotence or contraction identity is assumed.
-/

namespace Verification.GraphCoverMatrices

open Classical

open Verification.GraphCover Verification.GraphCoverFibers
  Verification.GraphCoverCoordinates Verification.GraphCoverCoordinateFacts
  Verification.GraphCoverOrder Verification.GraphCoverBoundaryParts
  Verification.GraphCoverBoundaryComparison Verification.EvenGraphBridge

variable {R V : Type*} [CommRing R] [Fintype V] [LinearOrder V]
  (G : SimpleGraph V) (C T : Finset V) (hC : Covers G C)

noncomputable def coefficientMatrix :
    Module.End R (Simplex G T →₀ R) ≃ₐ[R] Matrix (Simplex G T) (Simplex G T) R := by
  classical
  exact LinearMap.toMatrixAlgEquiv Finsupp.basisSingleOne

noncomputable def fiberMatrix :
    Module.End R (FiberProduct (R := R) G C T) ≃+*
      Matrix (Simplex G T) (Simplex G T) R :=
  (coefficientEquiv G C T hC).conjRingEquiv.trans (coefficientMatrix G T).toRingEquiv

theorem coefficientMatrix_apply (L : Module.End R (Simplex G T →₀ R)) (K J : Simplex G T) :
    coefficientMatrix G T L K J = L (Finsupp.single J 1) K := by
  classical
  simp [coefficientMatrix, LinearMap.toMatrixAlgEquiv_apply, Finsupp.basisSingleOne]

theorem fiberMatrix_apply (L : Module.End R (FiberProduct (R := R) G C T))
    (x y : Σ I : CoverSimplex G C T, Finset (RemainingVertex G C T I)) :
    fiberMatrix G C T hC L (fiberIndexEquiv G C T hC y) (fiberIndexEquiv G C T hC x) =
      Verification.ExteriorTotalBasis.coefficientEquiv
        (L (Pi.single x.1 (word (x.2.sort (· ≤ ·)))) y.1) y.2 := by
  classical
  change coefficientMatrix G T ((coefficientEquiv (R := R) G C T hC).conjRingEquiv L) _ _ = _
  rw [coefficientMatrix_apply]
  change coefficientEquiv G C T hC
    (L ((coefficientEquiv (R := R) G C T hC).symm
      (Finsupp.single (fiberIndexEquiv G C T hC x) 1))) (fiberIndexEquiv G C T hC y) = _
  rw [coefficientEquiv_symm_single, one_smul, coefficientEquiv_apply]

noncomputable def outsideMatrix : Matrix (Simplex G T) (Simplex G T) R :=
  coefficientMatrix G T (outsideBoundary G C T)

noncomputable def coverMatrix : Matrix (Simplex G T) (Simplex G T) R :=
  coefficientMatrix G T (coverBoundary G C T)

noncomputable def contractionMatrix : Matrix (Simplex G T) (Simplex G T) R :=
  fiberMatrix G C T hC (pureHomotopy G C T)

noncomputable def projectionMatrix : Matrix (Simplex G T) (Simplex G T) R :=
  fiberMatrix G C T hC (pureProjection G C T)

theorem outsideMatrix_fiber (hord : CoverOrdered C) :
    outsideMatrix (R := R) G C T = fiberMatrix G C T hC (pureBoundary G C T) := by
  rw [outsideMatrix, ← outside_conjugacy G C T hC hord]
  rfl

theorem boundaryMatrix_split :
    coefficientMatrix (R := R) G T (Verification.GraphSimplexChains.boundary G T) =
      outsideMatrix G C T + coverMatrix G C T := by
  rw [boundary_split, map_add]
  rfl

include hC in
theorem outsideMatrix_squared (hord : CoverOrdered C) :
    outsideMatrix (R := R) G C T * outsideMatrix G C T = 0 := by
  rw [outsideMatrix_fiber G C T hC hord, ← map_mul]
  change fiberMatrix G C T hC ((pureBoundary (R := R) G C T).comp (pureBoundary G C T)) = 0
  rw [pureBoundary_squared, map_zero]

theorem contractionMatrix_squared :
    contractionMatrix (R := R) G C T hC * contractionMatrix G C T hC = 0 := by
  rw [contractionMatrix, ← map_mul]
  change fiberMatrix G C T hC ((pureHomotopy (R := R) G C T).comp (pureHomotopy G C T)) = 0
  rw [pureHomotopy_squared, map_zero]

theorem contractionMatrix_regular (hord : CoverOrdered C) :
    contractionMatrix (R := R) G C T hC * outsideMatrix G C T * contractionMatrix G C T hC =
      contractionMatrix G C T hC := by
  rw [outsideMatrix_fiber G C T hC hord]
  simp only [contractionMatrix, ← map_mul, Module.End.mul_eq_comp, pureHomotopy_regular]

theorem outsideMatrix_regular (hord : CoverOrdered C) :
    outsideMatrix (R := R) G C T * contractionMatrix G C T hC * outsideMatrix G C T =
      outsideMatrix G C T := by
  rw [outsideMatrix_fiber G C T hC hord]
  simp only [contractionMatrix, ← map_mul, Module.End.mul_eq_comp, pureBoundary_regular]

theorem boundaryMatrix_squared :
    (outsideMatrix (R := R) G C T + coverMatrix G C T) *
      (outsideMatrix G C T + coverMatrix G C T) = 0 := by
  rw [← boundaryMatrix_split, ← map_mul]
  change coefficientMatrix G T ((Verification.GraphSimplexChains.boundary (R := R) G T).comp
    (Verification.GraphSimplexChains.boundary G T)) = 0
  rw [Verification.GraphSimplexChains.boundary_squared, map_zero]

theorem projectionMatrix_formula (hord : CoverOrdered C) :
    projectionMatrix (R := R) G C T hC =
      1 - outsideMatrix G C T * contractionMatrix G C T hC -
        contractionMatrix G C T hC * outsideMatrix G C T := by
  have hh := congrArg (fiberMatrix (R := R) G C T hC) (pure_homotopy_identity (R := R) G C T)
  simp only [← Module.End.mul_eq_comp, ← Module.End.one_eq_id,
    map_add, map_mul, map_sub, map_one] at hh
  rw [outsideMatrix_fiber G C T hC hord]
  change _ = 1 - fiberMatrix G C T hC (pureBoundary G C T) *
    fiberMatrix G C T hC (pureHomotopy G C T) -
    fiberMatrix G C T hC (pureHomotopy G C T) * fiberMatrix G C T hC (pureBoundary G C T)
  change fiberMatrix G C T hC (pureProjection G C T) = _
  rw [sub_sub]
  apply eq_sub_iff_add_eq.mpr
  simpa only [add_comm] using eq_sub_iff_add_eq.mp hh

theorem coverMatrix_raises (K J : Simplex G T)
    (hw : weight G C T K ≤ weight G C T J) : coverMatrix (R := R) G C T K J = 0 := by
  rw [coverMatrix, coefficientMatrix_apply]
  simp only [coverBoundary, Finsupp.linearCombination_single, one_smul]
  exact coverBasis_raises G C T J K hw

omit [Fintype V] in
open Classical in
theorem pureHomotopy_single (I : CoverSimplex G C T)
    (x : FiberExterior (R := R) G C T I) :
    pureHomotopy G C T (Pi.single I x) = Pi.single I (homotopyAt G C T I x) := by
  funext J
  by_cases h : J = I
  · subst J; simp [pureHomotopy]
  · simp [pureHomotopy, h]

theorem contractionMatrix_cover_ne
    (x y : Σ I : CoverSimplex G C T, Finset (RemainingVertex G C T I)) (h : y.1 ≠ x.1) :
    contractionMatrix (R := R) G C T hC (fiberIndexEquiv G C T hC y)
      (fiberIndexEquiv G C T hC x) = 0 := by
  classical
  rw [contractionMatrix, fiberMatrix_apply, pureHomotopy_single, Pi.single_eq_of_ne h]
  simp

theorem contractionMatrix_preserves_weight (K J : Simplex G T)
    (hw : weight G C T K ≠ weight G C T J) :
    contractionMatrix (R := R) G C T hC K J = 0 := by
  obtain ⟨x,rfl⟩ := (fiberIndexEquiv G C T hC).surjective J
  obtain ⟨y,rfl⟩ := (fiberIndexEquiv G C T hC).surjective K
  apply contractionMatrix_cover_ne G C T hC x y
  intro he
  apply hw
  change C.card - ((fiberIndexEquiv G C T hC ⟨y.1,y.2⟩).val ∩ C).card =
    C.card - ((fiberIndexEquiv G C T hC ⟨x.1,x.2⟩).val ∩ C).card
  rw [fiberIndex_cover, fiberIndex_cover, he]

#print axioms coefficientMatrix
#print axioms fiberMatrix
#print axioms coefficientMatrix_apply
#print axioms fiberMatrix_apply
#print axioms outsideMatrix
#print axioms coverMatrix
#print axioms contractionMatrix
#print axioms projectionMatrix
#print axioms outsideMatrix_fiber
#print axioms boundaryMatrix_split
#print axioms outsideMatrix_squared
#print axioms contractionMatrix_squared
#print axioms contractionMatrix_regular
#print axioms outsideMatrix_regular
#print axioms boundaryMatrix_squared
#print axioms projectionMatrix_formula
#print axioms coverMatrix_raises
#print axioms pureHomotopy_single
#print axioms contractionMatrix_cover_ne
#print axioms contractionMatrix_preserves_weight

end Verification.GraphCoverMatrices
