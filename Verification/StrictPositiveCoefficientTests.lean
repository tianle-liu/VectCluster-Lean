/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictCoefficientBoundaryEvaluation

/-!
# Strict Positive Coefficient Tests

Coefficient tests for a positive boundary use the canonical suspension
of the previous-degree test. This removes the outer inverse shift from
every actual differential contribution before evaluating Thom sections.
-/
noncomputable section
namespace Verification.StrictPositiveCoefficientTests
open CategoryTheory CategoryTheory.Limits
universe w
variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w} A]
variable {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]
variable [∀ n : ℤ, (shiftFunctor D n).Additive]
variable (J : DerivedCategory A ⥤ D) [J.CommShift ℤ]
variable (p : ℕ) (M : A)

def suspendTest (Y : D) :
    (Y ⟶ J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-(p : ℤ)) M))) ≃+
    (Y⟦(1 : ℤ)⟧ ⟶ J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-((p+1 : ℕ) : ℤ)) M))) where
  toFun a := (StrictCoefficientBoundaryEvaluation.shiftTest J p M _).symm
    ((shiftShiftNeg Y (1 : ℤ)).hom ≫ a)
  invFun b := (shiftShiftNeg Y (1 : ℤ)).inv ≫ StrictCoefficientBoundaryEvaluation.shiftTest J p M _ b
  left_inv a := by simp
  right_inv b := by simp
  map_add' a b := by simp only [Preadditive.comp_add, map_add]

theorem deshift_suspend (Y : D)
    (a : Y ⟶ J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-(p : ℤ)) M))) :
    StrictCoefficientBoundaryEvaluation.shiftTest J p M _ (suspendTest J p M Y a) =
      (shiftShiftNeg Y (1 : ℤ)).hom ≫ a := by
  exact (StrictCoefficientBoundaryEvaluation.shiftTest J p M _).apply_symm_apply _

theorem deshift_composite {X Y : D} (f : X ⟶ Y⟦(1 : ℤ)⟧)
    (a : Y ⟶ J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-(p : ℤ)) M))) :
    (StrictCoefficientBoundaryEvaluation.shiftTest J p M X).symm
      (f⟦(-1 : ℤ)⟧' ≫ (shiftShiftNeg Y (1 : ℤ)).hom ≫ a) =
    f ≫ suspendTest J p M Y a := by
  apply (StrictCoefficientBoundaryEvaluation.shiftTest J p M X).injective
  rw [AddEquiv.apply_symm_apply, StrictCoefficientBoundaryEvaluation.shiftTest_precomp, deshift_suspend]

#print axioms suspendTest
#print axioms deshift_suspend
#print axioms deshift_composite
end Verification.StrictPositiveCoefficientTests
