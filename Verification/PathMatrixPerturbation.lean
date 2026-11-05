/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathRhoFiltration
import Verification.PathZeroEndpointCoefficients
import Verification.PathCoefficientInclusion

/-!
# Path Matrix Perturbation

Literal finite matrices: the full path differential is its rho-zero
part plus a strictly lower-weight cochain perturbation. No associated-graded
identification or perturbation hypothesis is assumed.
-/

namespace Verification.PathMatrixPerturbation

open Classical Verification.PathCochains Verification.PathEndpointComplex
  Verification.PathEndpointWords Verification.PathNormalizedBasis
  Verification.PathEndpointCoordinates Verification.PathWeightFiltration
  Verification.PathRhoFiltration Verification.PathEndpointLeading
  Verification.PathZeroEndpointCoefficients

variable {R : Type*} [CommRing R]


theorem z_inverse_independent (ρ : R) (n : ℕ) (f : NormalIndex RightNormal n → R) :
    ((zCoefficients ρ n).symm f).val=((zCoefficients (0:R) n).symm f).val := by
  rw [Verification.PathCoefficientInclusion.z_inverse_val,Verification.PathCoefficientInclusion.z_inverse_val]

theorem y_inverse_independent (ρ : R) (a : ℕ) (f : NormalIndex BothNormal (2*a) → R) :
    ((yCoefficients ρ a).symm f).val=((yCoefficients (0:R) a).symm f).val := by
  rw [Verification.PathCoefficientInclusion.y_inverse_val,Verification.PathCoefficientInclusion.y_inverse_val]

theorem z_matrix_difference_strict (g ρ : R) (n : ℕ) (y x : NormalIndex RightNormal n)
    (h : weight x ≤ weight y) : (zMatrix g ρ n-zMatrix g 0 n) y x=0 := by
  simp only [Matrix.sub_apply,zMatrix,matrixOf,LinearMap.toMatrix'_apply,
    LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [show (fun i : NormalIndex RightNormal n => if i=x then (1 : R) else 0)=Pi.single x 1 by
    funext i; simp [Pi.single_apply,eq_comm]]
  rw [zCoefficients_apply,zCoefficients_apply]
  change (Verification.PathRightEndpoint.projection (endpointConstant ρ n)
    (differential g ρ n ((zCoefficients ρ n).symm (Pi.single x 1)).val y.1).val) y.2.val-
    (Verification.PathRightEndpoint.projection (endpointConstant (0:R) n)
    (differential g 0 n ((zCoefficients (0:R) n).symm (Pi.single x 1)).val y.1).val) y.2.val=0
  rw [z_inverse_independent,endpointConstant_zero]
  have hh := projected_difference_strict g ρ (endpointConstant ρ n) n (weight x)
    ((zCoefficients (0:R) n).symm (Pi.single x 1)).val (zCoefficients_inverse_bounded 0 n x) y.1
  exact (Finsupp.mem_supported' R _).mp hh y.2.val (by change ¬weight y < weight x; omega)

theorem y_matrix_difference_strict (g ρ : R) (a : ℕ) (y x : NormalIndex BothNormal (2*a))
    (h : weight x ≤ weight y) : (yMatrix g ρ a-yMatrix g 0 a) y x=0 := by
  simp only [Matrix.sub_apply,yMatrix,matrixOf,LinearMap.toMatrix'_apply,
    LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [show (fun i : NormalIndex BothNormal (2*a) => if i=x then (1 : R) else 0)=Pi.single x 1 by
    funext i; simp [Pi.single_apply,eq_comm]]
  rw [yCoefficients_apply,yCoefficients_apply]
  change (Verification.PathLeftEndpoint.projection 0
    (Verification.PathRightEndpoint.projection (endpointConstant ρ (2*a))
    (differential g ρ (2*a) ((yCoefficients ρ a).symm (Pi.single x 1)).val y.1).val)) y.2.val-
    (Verification.PathLeftEndpoint.projection 0
    (Verification.PathRightEndpoint.projection (endpointConstant (0:R) (2*a))
    (differential g 0 (2*a) ((yCoefficients (0:R) a).symm (Pi.single x 1)).val y.1).val)) y.2.val=0
  rw [y_inverse_independent,endpointConstant_zero]
  have hh := left_total_strict (0:R) (2*a) (weight x) _
    (projected_difference_strict g ρ (endpointConstant ρ (2*a)) (2*a) (weight x)
      ((yCoefficients (0:R) a).symm (Pi.single x 1)).val (yCoefficients_inverse_bounded 0 a x)) y.1
  simpa only [map_sub,Pi.sub_apply,Submodule.coe_sub,Finsupp.sub_apply] using
    (Finsupp.mem_supported' R _).mp hh y.2.val (by change ¬weight y < weight x; omega)

/-- Transposition recovers exactly the manuscript's strictly increasing chain weight. -/
theorem z_chain_difference_strict (g ρ : R) (n : ℕ) (y x : NormalIndex RightNormal n)
    (h : weight y ≤ weight x) : ((zMatrix g ρ n-zMatrix g 0 n).transpose) y x=0 :=
  z_matrix_difference_strict g ρ n x y h

theorem y_chain_difference_strict (g ρ : R) (a : ℕ) (y x : NormalIndex BothNormal (2*a))
    (h : weight y ≤ weight x) : ((yMatrix g ρ a-yMatrix g 0 a).transpose) y x=0 :=
  y_matrix_difference_strict g ρ a x y h

#print axioms z_inverse_independent
#print axioms y_inverse_independent
#print axioms z_matrix_difference_strict
#print axioms y_matrix_difference_strict
#print axioms z_chain_difference_strict
#print axioms y_chain_difference_strict

end Verification.PathMatrixPerturbation
