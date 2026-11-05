/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SingleLaurent
import Verification.LaurentPolynomialUniversal

/-!
# Single Laurent Polynomial Equiv

The two actual one-variable Laurent localizations agree, preserving the
coefficient algebra and the distinguished invertible coordinate.
-/
noncomputable section
namespace Verification.SingleLaurentPolynomialEquiv
variable (R : Type) [CommRing R]
def forward : SingleLaurent.Laurent.{0,0} R →ₐ[R] LaurentPolynomialUniversal.Laurent R :=
  SingleLaurent.lift (Algebra.ofId R _) (LaurentPolynomialUniversal.parameterUnit R)
def backward : LaurentPolynomialUniversal.Laurent R →ₐ[R] SingleLaurent.Laurent.{0,0} R :=
  LaurentPolynomialUniversal.lift (Algebra.ofId R _) (SingleLaurent.parameterUnit R)

theorem forward_parameter : forward R (SingleLaurent.parameter R)=LaurentPolynomialUniversal.parameter R := by
  rw [forward,SingleLaurent.lift_parameter,LaurentPolynomialUniversal.parameterUnit_val]
theorem backward_parameter : backward R (LaurentPolynomialUniversal.parameter R)=SingleLaurent.parameter R := by
  rw [backward,LaurentPolynomialUniversal.lift_parameter,SingleLaurent.parameterUnit_val]

theorem forward_backward : (forward R).comp (backward R)=AlgHom.id R _ := by
  apply LaurentPolynomialUniversal.hom_ext
  · intro r
    simp only [AlgHom.comp_apply,AlgHom.commutes,AlgHom.id_apply]
  · simp only [AlgHom.comp_apply,AlgHom.id_apply,backward_parameter,forward_parameter]

theorem backward_forward : (backward R).comp (forward R)=AlgHom.id R _ := by
  apply SingleLaurent.hom_ext
  · intro r
    simp only [AlgHom.comp_apply,AlgHom.commutes,AlgHom.id_apply]
  · simp only [AlgHom.comp_apply,AlgHom.id_apply,forward_parameter,backward_parameter]

def equiv : SingleLaurent.Laurent.{0,0} R ≃ₐ[R] LaurentPolynomialUniversal.Laurent R :=
  AlgEquiv.ofAlgHom (forward R) (backward R) (forward_backward R) (backward_forward R)

theorem parameter : equiv R (SingleLaurent.parameter R)=LaurentPolynomialUniversal.parameter R :=
  forward_parameter R

#print axioms forward
#print axioms backward
#print axioms forward_parameter
#print axioms backward_parameter
#print axioms forward_backward
#print axioms backward_forward
#print axioms equiv
#print axioms parameter
end Verification.SingleLaurentPolynomialEquiv
