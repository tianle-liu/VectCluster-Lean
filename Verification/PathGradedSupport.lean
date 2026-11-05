/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GradedRealizationNonpositive
import Verification.PathGradedSheafModel
import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# Path Graded Support

The positive path realization with its constant summand is genuinely
supported in nonpositive cochain degrees.
-/
noncomputable section
namespace Verification.PathGradedSupport
open CategoryTheory CategoryTheory.Limits
variable {C : Type*} [Category C] [Preadditive C] [HasFiniteBiproducts C]
  [HasBinaryBiproducts C] [HasZeroObject C]
variable (K : ℕ → C) (A : PathGradedCoefficientAction.Action (fun j=>K (j+1))) (Z : C)

theorem y (a : ℕ) : (PathGradedSheafModel.ySource K A Z a).IsStrictlyLE 0 := by
  apply (CochainComplex.isStrictlyLE_iff _ _).mpr
  intro p hp
  exact GradedRealizationNonpositive.withConstant K A (PathPositiveContraction.yData a) Z
    (fun i => by change -(i.1.val.card:ℤ)≤0;omega) p hp

theorem z (n : ℕ) : (PathGradedSheafModel.zSource K A Z n).IsStrictlyLE 0 := by
  apply (CochainComplex.isStrictlyLE_iff _ _).mpr
  intro p hp
  exact GradedRealizationNonpositive.withConstant K A (PathPositiveContraction.zData n) Z
    (fun i => by change -(i.1.val.card:ℤ)≤0;omega) p hp

#print axioms y
#print axioms z
end Verification.PathGradedSupport
