/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PositiveMatrixRestriction
import Verification.PathConstantBlock
import Verification.PathWeightedCellularSupport

/-!
# Path Positive Cross Terms

All omitted zero-weight cross terms vanish in the literal rectangular
path contraction, so restricting to positive MW weights preserves its inverse
and homotopy equations.
-/

namespace Verification.PathPositiveCrossTerms

open Classical Verification.PathCoefficientRing Verification.PathWeightFiltration
  Verification.PathSurvivorGrading Verification.PathConstantBlock Verification.PathZeroWeightIndex
  Verification.PathGradedFullReduction Verification.SurvivorBaseChange


theorem z_pure_I (n : ℕ) (i) (k : PathCokernel.Weight false (n+1)) (h : weight i≠k.val.val) :
    PathSurvivorMatrices.zInclusion n i k=0 := by
  rw [PathSurvivorMatrices.zInclusion,WeightedFixedBasis.inclusion_entry]
  exact zBasis_weight n k i h

theorem y_pure_I (a : ℕ) (i) (k : PathCokernel.Weight true (2*a)) (h : weight i≠k.val.val) :
    PathSurvivorMatrices.yInclusion a i k=0 := by
  rw [PathSurvivorMatrices.yInclusion,WeightedFixedBasis.inclusion_entry]
  exact yBasis_weight a k i h

theorem z_pure_J (n : ℕ) (k : PathCokernel.Weight false (n+1)) (i) (h : k.val.val≠weight i) :
    PathSurvivorMatrices.zRetraction n k i=0 := by
  change PathCoefficientGrading.pure (retractionMatrix (zProjection n)
    (PathSurvivorMatrices.zProjection_square n) (zBasis n) k i)=0
  rw [WeightedFixedBasis.retraction_support weight (fun k : PathCokernel.Weight false (n+1)=>k.val.val)
    _ _ _ (zProjection_weight n) (zBasis_weight n) k i h,map_zero]

theorem y_pure_J (a : ℕ) (k : PathCokernel.Weight true (2*a)) (i) (h : k.val.val≠weight i) :
    PathSurvivorMatrices.yRetraction a k i=0 := by
  change PathCoefficientGrading.pure (retractionMatrix (yProjection a)
    (PathSurvivorMatrices.yProjection_square a) (yBasis a) k i)=0
  rw [WeightedFixedBasis.retraction_support weight (fun k : PathCokernel.Weight true (2*a)=>k.val.val)
    _ _ _ (yProjection_weight a) (yBasis_weight a) k i h,map_zero]

theorem z_I (n : ℕ) (i) (k : PathCokernel.Weight false (n+1)) (hi : 0<weight i) (hk : k.val.val=0) :
    PathWeightedFullMatrices.zInclusion n i k=0 :=
  PositiveMatrixRestriction.positive_inclusion weight (fun k : PathCokernel.Weight false (n+1)=>k.val.val)
    (zIndex n) (zIndex_weight n) (z_unique n) _ _ (z_full_isolated n).2.1.2 (z_pure_I n) i k hi hk

theorem y_I (a : ℕ) (i) (k : PathCokernel.Weight true (2*a)) (hi : 0<weight i) (hk : k.val.val=0) :
    PathWeightedFullMatrices.yInclusion a i k=0 :=
  PositiveMatrixRestriction.positive_inclusion weight (fun k : PathCokernel.Weight true (2*a)=>k.val.val)
    (yIndex a) (yIndex_weight a) (y_unique a) _ _ (y_full_isolated a).2.1.2 (y_pure_I a) i k hi hk

theorem z_J (n : ℕ) (k : PathCokernel.Weight false (n+1)) (i) (hk : 0<k.val.val) (hi : weight i=0) :
    PathWeightedFullMatrices.zRetraction n k i=0 :=
  PositiveMatrixRestriction.positive_retraction weight (fun k : PathCokernel.Weight false (n+1)=>k.val.val)
    (zIndex n) (zIndex_weight n) (z_unique n) _ _ (z_full_isolated n).2.2.2 (z_pure_J n) k i hk hi

theorem y_J (a : ℕ) (k : PathCokernel.Weight true (2*a)) (i) (hk : 0<k.val.val) (hi : weight i=0) :
    PathWeightedFullMatrices.yRetraction a k i=0 :=
  PositiveMatrixRestriction.positive_retraction weight (fun k : PathCokernel.Weight true (2*a)=>k.val.val)
    (yIndex a) (yIndex_weight a) (y_unique a) _ _ (y_full_isolated a).2.2.2 (y_pure_J a) k i hk hi

theorem z_D (n : ℕ) (i) (j) (hj : weight j=0) :
    (Verification.PathEndpointCoordinates.zMatrix g rho n).transpose i j=0 := by
  rw [z_unique n j hj]
  have he := congrArg (fun M=>M i (zIndex n)) (z_differential rho n).2
  simpa [zConstant,ZeroWeightMatrixBlock.constantProjection,Matrix.mul_diagonal] using he

theorem y_D (a : ℕ) (i) (j) (hj : weight j=0) :
    (Verification.PathEndpointCoordinates.yMatrix g rho a).transpose i j=0 := by
  rw [y_unique a j hj]
  have he := congrArg (fun M=>M i (yIndex a)) (y_differential rho a).2
  simpa [yConstant,ZeroWeightMatrixBlock.constantProjection,Matrix.mul_diagonal] using he

theorem z_H (n : ℕ) (i) (j) (hj : weight j=0) : (zReduction n).homotopy i j=0 := by
  rw [z_unique n j hj]
  have he := congrArg (fun M=>M i (zIndex n)) (z_full_isolated n).1.2
  simpa [zConstant,ZeroWeightMatrixBlock.constantProjection,Matrix.mul_diagonal] using he

theorem y_H (a : ℕ) (i) (j) (hj : weight j=0) : (yReduction a).homotopy i j=0 := by
  rw [y_unique a j hj]
  have he := congrArg (fun M=>M i (yIndex a)) (y_full_isolated a).1.2
  simpa [yConstant,ZeroWeightMatrixBlock.constantProjection,Matrix.mul_diagonal] using he

#print axioms z_pure_I
#print axioms y_pure_I
#print axioms z_pure_J
#print axioms y_pure_J
#print axioms z_I
#print axioms y_I
#print axioms z_J
#print axioms y_J
#print axioms z_D
#print axioms y_D
#print axioms z_H
#print axioms y_H

end Verification.PathPositiveCrossTerms
