/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathWeightedFullMatrices

/-!
# Path Weighted Cellular Support

The actual rectangular weighted splitting also preserves cellular degree:
its finite free survivor is concentrated in degree zero.
-/

namespace Verification.PathWeightedCellularSupport

open Classical Verification.PathCoefficientRing Verification.PathEndpointCoordinates
  Verification.PathStratumGrading Verification.PathPureSpecialization Verification.PathSurvivorGrading
  Verification.SurvivorBaseChange Verification.PathGradedFullReduction

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem inverse_column_zero (P : Matrix ι ι Coeff) (hP : P*P=P)
    (b : Basis κ Coeff (fixedModule P)) (j : ι) (hp : ∀i,P i j=0) (k : κ) :
    retractionMatrix P hP b k j=0 := by
  have hx : projection P hP (fun l=>if l=j then 1 else 0)=0 := by
    apply Subtype.ext
    funext i
    change (∑l,P i l*(if l=j then 1 else 0))=0
    simpa using hp i
  simp only [retractionMatrix,LinearMap.toMatrix'_apply,LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap,hx,map_zero,Pi.zero_apply]

theorem z_pure_inclusion (n : ℕ) (i) (k) (hi : -degree i≠0) :
    PathSurvivorMatrices.zInclusion n i k=0 := by
  rw [PathSurvivorMatrices.zInclusion,WeightedFixedBasis.inclusion_entry]
  exact (PathWeightedSurvivors.zBasis_entry g g_square n (zData n).toData k i).trans
    (by rw [(zData n).supported i _ hi,zero_mul])

theorem y_pure_inclusion (a : ℕ) (i) (k) (hi : -degree i≠0) :
    PathSurvivorMatrices.yInclusion a i k=0 := by
  rw [PathSurvivorMatrices.yInclusion,WeightedFixedBasis.inclusion_entry]
  exact (PathWeightedSurvivors.yBasis_entry g g_square a (yData a).toData k i).trans
    (by rw [(yData a).supported i _ hi,zero_mul])

theorem z_pure_retraction (n : ℕ) (k) (j) (hj : -degree j≠0) :
    PathSurvivorMatrices.zRetraction n k j=0 := by
  have hp : ∀i,zProjection n i j=0 := by
    intro i
    by_cases hi : -degree i=0
    · exact (zReduction n).projection_degree i j (by omega)
    · exact (zData n).supported i j hi
  change PathCoefficientGrading.pure (retractionMatrix (zProjection n)
    (PathSurvivorMatrices.zProjection_square n) (zBasis n) k j)=0
  rw [inverse_column_zero _ _ _ j hp k,map_zero]

theorem y_pure_retraction (a : ℕ) (k) (j) (hj : -degree j≠0) :
    PathSurvivorMatrices.yRetraction a k j=0 := by
  have hp : ∀i,yProjection a i j=0 := by
    intro i
    by_cases hi : -degree i=0
    · exact (yReduction a).projection_degree i j (by omega)
    · exact (yData a).supported i j hi
  change PathCoefficientGrading.pure (retractionMatrix (yProjection a)
    (PathSurvivorMatrices.yProjection_square a) (yBasis a) k j)=0
  rw [inverse_column_zero _ _ _ j hp k,map_zero]

theorem z_inclusion (n : ℕ) (i) (k) (hi : -degree i≠0) :
    PathWeightedFullMatrices.zInclusion n i k=0 := by
  change ∑j,(zReduction n).inclusion i j*PathSurvivorMatrices.zInclusion n j k=0
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : -degree j=0
  · rw [(zReduction n).degreeI i j (by omega),zero_mul]
  · rw [z_pure_inclusion n j k hj,mul_zero]

theorem y_inclusion (a : ℕ) (i) (k) (hi : -degree i≠0) :
    PathWeightedFullMatrices.yInclusion a i k=0 := by
  change ∑j,(yReduction a).inclusion i j*PathSurvivorMatrices.yInclusion a j k=0
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : -degree j=0
  · rw [(yReduction a).degreeI i j (by omega),zero_mul]
  · rw [y_pure_inclusion a j k hj,mul_zero]

theorem z_retraction (n : ℕ) (k) (j) (hj : -degree j≠0) :
    PathWeightedFullMatrices.zRetraction n k j=0 := by
  change ∑i,PathSurvivorMatrices.zRetraction n k i*(zReduction n).retraction i j=0
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : -degree i=0
  · rw [(zReduction n).degreeJ i j (by omega),mul_zero]
  · rw [z_pure_retraction n k i hi,zero_mul]

theorem y_retraction (a : ℕ) (k) (j) (hj : -degree j≠0) :
    PathWeightedFullMatrices.yRetraction a k j=0 := by
  change ∑i,PathSurvivorMatrices.yRetraction a k i*(yReduction a).retraction i j=0
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : -degree i=0
  · rw [(yReduction a).degreeJ i j (by omega),mul_zero]
  · rw [y_pure_retraction a k i hi,zero_mul]

#print axioms inverse_column_zero
#print axioms z_pure_inclusion
#print axioms y_pure_inclusion
#print axioms z_pure_retraction
#print axioms y_pure_retraction
#print axioms z_inclusion
#print axioms y_inclusion
#print axioms z_retraction
#print axioms y_retraction

end Verification.PathWeightedCellularSupport
