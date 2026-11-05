/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathSurvivorMatrices
import Verification.RectangularResidualRetraction

/-!
# Path Weighted Full Matrices

The all-length full-rho path contraction is now written in the original
weight-labelled finite free survivor basis, with both coefficient gradings
and every rectangular homotopy identity verified.
-/

namespace Verification.PathWeightedFullMatrices

open Verification.PathCoefficientRing Verification.PathEndpointCoordinates
  Verification.PathWeightFiltration Verification.PathSurvivorMatrices
  Verification.PathSurvivorGrading Verification.PathGradedFullReduction

noncomputable def zInclusion (n : ℕ) := (zReduction n).inclusion*PathSurvivorMatrices.zInclusion n
noncomputable def yInclusion (a : ℕ) := (yReduction a).inclusion*PathSurvivorMatrices.yInclusion a
noncomputable def zRetraction (n : ℕ) := PathSurvivorMatrices.zRetraction n*(zReduction n).retraction
noncomputable def yRetraction (a : ℕ) := PathSurvivorMatrices.yRetraction a*(yReduction a).retraction

theorem zInclusion_degree (n : ℕ) : PathGradedMatrices.Homogeneous
    (fun i=>(weight i:ℤ)) (fun k=>(k.val.val:ℤ)) (zInclusion n) :=
  PathGradedMatrices.mul _ _ _ _ _ (z_coefficients n).2.1 (PathSurvivorMatrices.zInclusion_degree n)

theorem yInclusion_degree (a : ℕ) : PathGradedMatrices.Homogeneous
    (fun i=>(weight i:ℤ)) (fun k=>(k.val.val:ℤ)) (yInclusion a) :=
  PathGradedMatrices.mul _ _ _ _ _ (y_coefficients a).2.1 (PathSurvivorMatrices.yInclusion_degree a)

theorem zRetraction_degree (n : ℕ) : PathGradedMatrices.Homogeneous
    (fun k=>(k.val.val:ℤ)) (fun i=>(weight i:ℤ)) (zRetraction n) :=
  PathGradedMatrices.mul _ _ _ _ _ (PathSurvivorMatrices.zRetraction_degree n) (z_coefficients n).2.2

theorem yRetraction_degree (a : ℕ) : PathGradedMatrices.Homogeneous
    (fun k=>(k.val.val:ℤ)) (fun i=>(weight i:ℤ)) (yRetraction a) :=
  PathGradedMatrices.mul _ _ _ _ _ (PathSurvivorMatrices.yRetraction_degree a) (y_coefficients a).2.2

theorem z_retraction_inclusion (n : ℕ) : zRetraction n*zInclusion n=1 :=
  RectangularResidualRetraction.retraction_inclusion _ _ _ (zReduction n) _ _
    (PathSurvivorMatrices.z_inclusion_retraction n) (PathSurvivorMatrices.z_retraction_inclusion n)

theorem y_retraction_inclusion (a : ℕ) : yRetraction a*yInclusion a=1 :=
  RectangularResidualRetraction.retraction_inclusion _ _ _ (yReduction a) _ _
    (PathSurvivorMatrices.y_inclusion_retraction a) (PathSurvivorMatrices.y_retraction_inclusion a)

theorem z_homotopy_identity (n : ℕ) : zInclusion n*zRetraction n=
    1-(zMatrix g rho n).transpose*(zReduction n).homotopy-
      (zReduction n).homotopy*(zMatrix g rho n).transpose :=
  RectangularResidualRetraction.homotopy_identity _ _ _ (zReduction n) _ _
    (PathSurvivorMatrices.z_inclusion_retraction n)

theorem y_homotopy_identity (a : ℕ) : yInclusion a*yRetraction a=
    1-(yMatrix g rho a).transpose*(yReduction a).homotopy-
      (yReduction a).homotopy*(yMatrix g rho a).transpose :=
  RectangularResidualRetraction.homotopy_identity _ _ _ (yReduction a) _ _
    (PathSurvivorMatrices.y_inclusion_retraction a)

theorem z_inclusion_chain (n : ℕ) : (zMatrix g rho n).transpose*zInclusion n=0 :=
  RectangularResidualRetraction.inclusion_chain _ _ _ (zReduction n) _ (z_residual_zero n)

theorem y_inclusion_chain (a : ℕ) : (yMatrix g rho a).transpose*yInclusion a=0 :=
  RectangularResidualRetraction.inclusion_chain _ _ _ (yReduction a) _ (y_residual_zero a)

theorem z_retraction_chain (n : ℕ) : zRetraction n*(zMatrix g rho n).transpose=0 :=
  RectangularResidualRetraction.retraction_chain _ _ _ (zReduction n) _ (z_residual_zero n)

theorem y_retraction_chain (a : ℕ) : yRetraction a*(yMatrix g rho a).transpose=0 :=
  RectangularResidualRetraction.retraction_chain _ _ _ (yReduction a) _ (y_residual_zero a)

#print axioms zInclusion
#print axioms yInclusion
#print axioms zRetraction
#print axioms yRetraction
#print axioms zInclusion_degree
#print axioms yInclusion_degree
#print axioms zRetraction_degree
#print axioms yRetraction_degree
#print axioms z_retraction_inclusion
#print axioms y_retraction_inclusion
#print axioms z_homotopy_identity
#print axioms y_homotopy_identity
#print axioms z_inclusion_chain
#print axioms y_inclusion_chain
#print axioms z_retraction_chain
#print axioms y_retraction_chain

end Verification.PathWeightedFullMatrices
