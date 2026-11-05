/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.WeightedConstantTerms

/-!
# Graded Realization Nonpositive

Positive-weight realization and its independent constant complex have
no positive cochain terms when the original degree function is nonpositive.
-/
noncomputable section
namespace Verification.GradedRealizationNonpositive
open Classical CategoryTheory CategoryTheory.Limits
variable {C : Type*} [Category C] [Preadditive C] [HasFiniteBiproducts C]
  [HasBinaryBiproducts C] [HasZeroObject C]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {w : ι → ℕ} {v : κ → ℕ} {d : ι → ℤ}
variable (K : ℕ → C) (A : PathGradedCoefficientAction.Action (fun j=>K (j+1)))
variable (T : PositiveGradedContraction.Data w v d) (Z : C)

omit [HasBinaryBiproducts C] [HasZeroObject C] in
theorem positive (hd : ∀ i,d i≤0) (p : ℤ) (hp : 0<p) :
    IsZero ((GradedCoefficientRealization.source K A T).X p) := by
  apply IsZero.of_iso _ (GradedCoefficientRealization.sourceTermIso K A T p)
  apply (IsZero.iff_id_eq_zero _).mpr
  apply biproduct.hom_ext
  intro i
  have h := hd i.val.val
  rw [i.property] at h
  omega

theorem withConstant (hd : ∀ i,d i≤0) (p : ℤ) (hp : 0<p) :
    IsZero ((GradedCoefficientRealization.withConstant K A T Z).X p) := by
  apply IsZero.of_iso _ (HomologicalComplex.biprodXIso _ _ p)
  exact (biprod_isZero_iff _ _).mpr
    ⟨HomologicalComplex.isZero_single_obj_X _ 0 Z p (ne_of_gt hp),positive K A T hd p hp⟩

#print axioms positive
#print axioms withConstant
end Verification.GradedRealizationNonpositive
