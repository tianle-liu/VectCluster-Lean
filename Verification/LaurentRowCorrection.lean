/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LaurentMutableScaling
import Mathlib.Data.Matrix.Mul

/-!
# Laurent Row Correction

The manuscript's literal integer identity C1=Cstd+UP gives a global
Laurent exchange-algebra equivalence by x_i=t^(-U_i)X_i.
-/
noncomputable section
namespace Verification.LaurentRowCorrection
open scoped BigOperators
variable (R : Type*) [CommRing R] {V F : Type*} [Fintype V]
variable (P : Matrix V V ℤ) (C₀ C₁ U : Matrix F V ℤ)
variable (hC : C₁=C₀+U*P)

def column (C : Matrix F V ℤ) (i : V) : F → ℤ := fun f=>C f i

def rescaling (i : V) : F → ℤ := -(column U i)

include hC in
theorem transformed_eq : LaurentMutableScaling.transformed P (column C₁) (rescaling U)=column C₀ := by
  funext i f
  change C₁ f i+(∑ r,P r i • -(column U r)) f=C₀ f i
  rw [hC]
  simp only [Matrix.add_apply,Matrix.mul_apply,Finset.sum_apply,Pi.smul_apply,Pi.neg_apply,column,zsmul_eq_mul,Pi.mul_apply,Pi.intCast_apply,Int.cast_id]
  rw [show (∑ r,P r i*(-U f r))=-(∑ r,U f r*P r i) by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro r _
    ring]
  ring

def presentationEquiv (c : V → Rˣ) :
    LaurentScalarModel.Presentation R P (column C₁) c ≃ₐ[R]
      LaurentScalarModel.Presentation R P (column C₀) c :=
  (LaurentMutableScaling.presentationEquiv R P (column C₁) c (rescaling U)).trans
    (Ideal.quotientEquivAlgOfEq R (congrArg (fun f=>LaurentScalarModel.relations R P f c)
      (transformed_eq P C₀ C₁ U hC)))

theorem presentation_original (c : V → Rˣ) (i : V) :
    presentationEquiv R P C₀ C₁ U hC c (Ideal.Quotient.mk _ (MvPolynomial.C (MvPolynomial.X i)))=
      algebraMap (LaurentScalarModel.Coefficients R (F → ℤ)) _ (ExchangeCharacters.monomial (-(column U i)))*
        (Ideal.Quotient.mk _ (MvPolynomial.C (MvPolynomial.X i)) : LaurentScalarModel.Presentation R P (column C₀) c) := by
  change Ideal.Quotient.mk _ (TwoTermCoordinateScaling.ambient (LaurentScalarModel.Coefficients R (F → ℤ)) id
    (fun r=>LaurentMutableScaling.monomialUnit R (rescaling U r)) (LaurentMutableScaling.common R P (rescaling U))
      (MvPolynomial.C (MvPolynomial.X i)))=_
  rw [TwoTermCoordinateScaling.ambient_original,map_mul]
  rfl

#print axioms column
#print axioms rescaling
#print axioms transformed_eq
#print axioms presentationEquiv
#print axioms presentation_original
end Verification.LaurentRowCorrection
