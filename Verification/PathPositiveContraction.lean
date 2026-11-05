/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PositiveGradedContraction
import Verification.PathPositiveCrossTerms

/-!
# Path Positive Contraction

Actual all-length positive-weight path contractions. Every algebraic,
cellular-degree and coefficient-degree input to the categorical realization
is supplied by a proved property of the manuscript's literal full-rho matrix.
-/

noncomputable section
namespace Verification.PathPositiveContraction

open Classical Verification.PathCoefficientRing Verification.PathEndpointCoordinates
  Verification.PathWeightFiltration Verification.PathStratumGrading Verification.PathGradedFullReduction
  Verification.PathWeightedFullMatrices Verification.PathWeightedCellularSupport


def zData (n : ℕ) : PositiveGradedContraction.Data
    (ι:=PathNormalizedBasis.NormalIndex PathEndpointWords.RightNormal n) weight
    (fun k : PathCokernel.Weight false (n+1)=>k.val.val) (fun i=>-degree i) where
  D := (zMatrix g rho n).transpose
  H := (zReduction n).homotopy
  I := PathWeightedFullMatrices.zInclusion n
  J := PathWeightedFullMatrices.zRetraction n
  coefficientD := PathMatrixCoefficientGrading.z_chain_degree n
  coefficientH := (z_coefficients n).1
  coefficientI := zInclusion_degree n
  coefficientJ := zRetraction_degree n
  degreeD := (zReduction n).degreeD
  degreeH := (zReduction n).degreeH
  degreeI := PathWeightedCellularSupport.z_inclusion n
  degreeJ := PathWeightedCellularSupport.z_retraction n
  square := (zReduction n).squareD
  chainI := z_inclusion_chain n
  chainJ := z_retraction_chain n
  retract := z_retraction_inclusion n
  homotopy := z_homotopy_identity n
  crossD := fun i j _ hj=>PathPositiveCrossTerms.z_D n i j hj
  crossH := fun i j _ hj=>PathPositiveCrossTerms.z_H n i j hj
  crossI := PathPositiveCrossTerms.z_I n
  crossJ := PathPositiveCrossTerms.z_J n

def yData (a : ℕ) : PositiveGradedContraction.Data
    (ι:=PathNormalizedBasis.NormalIndex PathEndpointWords.BothNormal (2*a)) weight
    (fun k : PathCokernel.Weight true (2*a)=>k.val.val) (fun i=>-degree i) where
  D := (yMatrix g rho a).transpose
  H := (yReduction a).homotopy
  I := PathWeightedFullMatrices.yInclusion a
  J := PathWeightedFullMatrices.yRetraction a
  coefficientD := PathMatrixCoefficientGrading.y_chain_degree a
  coefficientH := (y_coefficients a).1
  coefficientI := yInclusion_degree a
  coefficientJ := yRetraction_degree a
  degreeD := (yReduction a).degreeD
  degreeH := (yReduction a).degreeH
  degreeI := PathWeightedCellularSupport.y_inclusion a
  degreeJ := PathWeightedCellularSupport.y_retraction a
  square := (yReduction a).squareD
  chainI := y_inclusion_chain a
  chainJ := y_retraction_chain a
  retract := y_retraction_inclusion a
  homotopy := y_homotopy_identity a
  crossD := fun i j _ hj=>PathPositiveCrossTerms.y_D a i j hj
  crossH := fun i j _ hj=>PathPositiveCrossTerms.y_H a i j hj
  crossI := PathPositiveCrossTerms.y_I a
  crossJ := PathPositiveCrossTerms.y_J a

/-- A genuine graded-category homotopy equivalence for every Z path length. -/
def zEquivalence (n : ℕ) := PositiveGradedContraction.equivalence (zData n)

/-- A genuine graded-category homotopy equivalence for every even Y length. -/
def yEquivalence (a : ℕ) := PositiveGradedContraction.equivalence (yData a)

#print axioms zData
#print axioms yData
#print axioms zEquivalence
#print axioms yEquivalence

end Verification.PathPositiveContraction
