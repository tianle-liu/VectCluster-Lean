/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathPureWeight

/-!
# Path Pure Matrix Weight

Exact weight preservation of the actual finite pure path matrices.
-/

namespace Verification.PathPureMatrixWeight

open Classical Verification.PathCochains Verification.PathEndpointComplex
  Verification.PathEndpointWords Verification.PathNormalizedBasis
  Verification.PathEndpointCoordinates Verification.PathWeightFiltration
  Verification.PathPureWeight Verification.PathZeroEndpointCoefficients

variable {R : Type*} [CommRing R]

theorem z_matrix_exact_weight (g : R) (n : ℕ) (y x : NormalIndex RightNormal n)
    (h : weight y ≠ weight x) : zMatrix g 0 n y x=0 := by
  simp only [zMatrix,matrixOf,LinearMap.toMatrix'_apply,LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [show (fun i : NormalIndex RightNormal n => if i=x then (1 : R) else 0)=Pi.single x 1 by
    funext i; simp [Pi.single_apply,eq_comm]]
  rw [zCoefficients_apply]
  change (Verification.PathRightEndpoint.projection (endpointConstant (0:R) n)
    (differential g 0 n ((zCoefficients (0:R) n).symm (Pi.single x 1)).val y.1).val) y.2.val=0
  rw [endpointConstant_zero,right_zero_coefficient y.2.val y.2.property.2 _]
  have hx : TotalExact n (weight x) ((zCoefficients (0:R) n).symm (Pi.single x 1)).val :=
    normal_inverse_exact RightNormal n x
  exact (Finsupp.mem_supported' R _).mp (differential_exact g n (weight x) _ hx y.1) y.2.val h

theorem y_matrix_exact_weight (g : R) (a : ℕ) (y x : NormalIndex BothNormal (2*a))
    (h : weight y ≠ weight x) : yMatrix g 0 a y x=0 := by
  simp only [yMatrix,matrixOf,LinearMap.toMatrix'_apply,LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [show (fun i : NormalIndex BothNormal (2*a) => if i=x then (1 : R) else 0)=Pi.single x 1 by
    funext i; simp [Pi.single_apply,eq_comm]]
  rw [yCoefficients_apply]
  change (Verification.PathLeftEndpoint.projection 0
    (Verification.PathRightEndpoint.projection (endpointConstant (0:R) (2*a))
    (differential g 0 (2*a) ((yCoefficients (0:R) a).symm (Pi.single x 1)).val y.1).val)) y.2.val=0
  rw [endpointConstant_zero,left_zero_coefficient y.2.val y.2.property.2.1 _,
    right_zero_coefficient y.2.val y.2.property.2.2 _]
  have hx : TotalExact (2*a) (weight x) ((yCoefficients (0:R) a).symm (Pi.single x 1)).val :=
    normal_inverse_exact BothNormal (2*a) x
  exact (Finsupp.mem_supported' R _).mp (differential_exact g (2*a) (weight x) _ hx y.1) y.2.val h

#print axioms z_matrix_exact_weight
#print axioms y_matrix_exact_weight

end Verification.PathPureMatrixWeight
