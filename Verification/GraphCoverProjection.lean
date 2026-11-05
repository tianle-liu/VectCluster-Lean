/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GraphCoverGrading

/-!
# Graph Cover Projection

Exact survivor coordinates for the graph-cover projection.
-/

namespace Verification.GraphCoverProjection

open Classical
open Verification.GraphCover Verification.GraphCoverFibers
  Verification.GraphCoverCoordinates Verification.GraphCoverCoordinateFacts
  Verification.GraphCoverOrder Verification.GraphCoverBoundaryParts
  Verification.GraphCoverMatrices Verification.GraphCoverGrading
  Verification.EvenGraphBridge Verification.GradedPerturbation
  Verification.PerturbedHomologyModel

variable {R V : Type*} [CommRing R] [Fintype V] [LinearOrder V]
  (G : SimpleGraph V) (C T : Finset V) (hC : Covers G C)

omit [Fintype V] in
theorem pureProjection_single (I : CoverSimplex G C T)
    (x : FiberExterior (R := R) G C T I) :
    pureProjection G C T (Pi.single I x) = Pi.single I (projectionAt G C T I x) := by
  funext J
  by_cases h : J = I
  · subst J; simp [pureProjection]
  · simp [pureProjection, h]

theorem projection_on_single
    (x : Σ I : CoverSimplex G C T, Finset (RemainingVertex G C T I)) :
    (coefficientEquiv (R := R) G C T hC).conjRingEquiv (pureProjection G C T)
      (Finsupp.single (fiberIndexEquiv G C T hC x) 1) =
    if Survives G C T (fiberIndexEquiv G C T hC x) then
      Finsupp.single (fiberIndexEquiv G C T hC x) 1 else 0 := by
  rcases x with ⟨I,A⟩
  change coefficientEquiv G C T hC (pureProjection G C T
    ((coefficientEquiv (R := R) G C T hC).symm
      (Finsupp.single (fiberIndexEquiv G C T hC ⟨I,A⟩) 1))) = _
  rw [coefficientEquiv_symm_single, one_smul, pureProjection_single]
  have hs : Survives G C T (fiberIndexEquiv G C T hC ⟨I,A⟩) ↔
      ¬(remaining G C T I.val).Nonempty := by
    rw [survives_iff_empty_remaining G C T, fiberIndex_cover,
      Finset.not_nonempty_iff_eq_empty]
  by_cases hn : (remaining G C T I.val).Nonempty
  · have hns : ¬Survives G C T (fiberIndexEquiv G C T hC ⟨I,A⟩) := fun h => hs.mp h hn
    rw [if_neg hns]
    simp only [projectionAt, if_pos hn, LinearMap.zero_apply, Pi.single_zero]
    exact (coefficientEquiv (R := R) G C T hC).map_zero
  · rw [if_pos (hs.mpr hn)]
    simp only [projectionAt, if_neg hn, LinearMap.id_apply]
    simpa only [one_smul] using coefficientEquiv_single_word G C T hC ⟨I,A⟩ (1 : R)

theorem projectionMatrix_diagonal :
    projectionMatrix (R := R) G C T hC =
      Matrix.diagonal (fun J : Simplex G T => if Survives G C T J then 1 else 0) := by
  ext K J
  obtain ⟨x,rfl⟩ := (fiberIndexEquiv G C T hC).surjective J
  change coefficientMatrix G T
    ((coefficientEquiv (R := R) G C T hC).conjRingEquiv (pureProjection G C T)) K _ = _
  rw [coefficientMatrix_apply, projection_on_single]
  by_cases he : K = fiberIndexEquiv G C T hC x
  · subst K
    by_cases hs : Survives G C T (fiberIndexEquiv G C T hC x) <;>
      simp [hs, Matrix.diagonal_apply, Finsupp.single_apply, eq_comm]
  · by_cases hs : Survives G C T (fiberIndexEquiv G C T hC x) <;>
      simp [hs, he, Matrix.diagonal_apply, Finsupp.single_apply, eq_comm]

theorem projectionMatrix_mulVec (x : Simplex G T → R) (J : Simplex G T) :
    (projectionMatrix G C T hC).mulVec x J = if Survives G C T J then x J else 0 := by
  rw [projectionMatrix_diagonal, Matrix.mulVec_diagonal]
  by_cases h : Survives G C T J <;> simp [h]

/-- Concrete survivor indices in a fixed cochain degree. -/
abbrev SurvivorIndex (p : ℤ) := {J : Simplex G T // Survives G C T J ∧ degree G T J = p}

noncomputable def fixedCoordinateEquiv (p : ℤ) :
    fixedModule (degree G T) (projectionMatrix (R := R) G C T hC) p ≃ₗ[R]
      (SurvivorIndex G C T p → R) where
  toFun x J := x.val J.val
  invFun f := ⟨fun J => if h : Survives G C T J ∧ degree G T J = p then f ⟨J,h⟩ else 0,
    ⟨by intro J h; simp [h], by
      funext J
      rw [projectionMatrix_mulVec]
      by_cases hs : Survives G C T J <;> simp [hs]⟩⟩
  left_inv x := by
    apply Subtype.ext
    funext J
    by_cases h : Survives G C T J ∧ degree G T J = p
    · simp [h]
    · simp only [dif_neg h]
      by_cases hs : Survives G C T J
      · exact (x.property.1 J (fun hd => h ⟨hs,hd⟩)).symm
      · have hx := congrFun x.property.2 J
        rw [projectionMatrix_mulVec, if_neg hs] at hx
        exact hx
  right_inv f := by funext J; simp [J.property]
  map_add' x y := rfl
  map_smul' r x := rfl

noncomputable def survivorBasis (p : ℤ) :
    Basis (SurvivorIndex G C T p) R
      (fixedModule (degree G T) (projectionMatrix (R := R) G C T hC) p) :=
  (Pi.basisFun R _).map (fixedCoordinateEquiv G C T hC p).symm

omit [Fintype V] in
theorem survivor_degree_range (p : ℤ) (J : SurvivorIndex G C T p) :
    -(coverRank G C : ℤ) ≤ p ∧ p ≤ 0 := by
  have hc := survivor_degree_bound G C T J.val J.property.1
  have hd := J.property.2
  simp only [degree] at hd
  omega

#print axioms pureProjection_single
#print axioms projection_on_single
#print axioms projectionMatrix_diagonal
#print axioms projectionMatrix_mulVec
#print axioms SurvivorIndex
#print axioms fixedCoordinateEquiv
#print axioms survivorBasis
#print axioms survivor_degree_range

end Verification.GraphCoverProjection
