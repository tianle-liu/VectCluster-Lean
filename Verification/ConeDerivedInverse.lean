/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ConeDerivedComparison

/-!
# Cone Derived Inverse

The inverse of a genuine cone isomorphism is the cone map of the
inverse commuting square. This is proved before substituting large
geometric coordinate constructions.
-/
noncomputable section
namespace Verification.ConeDerivedInverse
open CategoryTheory CategoryTheory.Limits CochainComplex
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable {U₁ W₁ U₂ W₂ : CochainComplex C ℤ}
variable (j₁ : U₁ ⟶ W₁) (j₂ : U₂ ⟶ W₂)
variable (u : U₁ ≅ U₂) (v : W₁ ≅ W₂) (h : j₁ ≫ v.hom = u.hom ≫ j₂)

include h in
omit [HasBinaryBiproducts C] [HasDerivedCategory C] in
theorem inverse_square : j₂ ≫ v.inv = u.inv ≫ j₁ := by
  apply (cancel_epi u.hom).mp
  rw [Iso.hom_inv_id_assoc,← Category.assoc,← h,Category.assoc,Iso.hom_inv_id,Category.comp_id]

theorem inverse : (ConeDerivedComparison.coneIso j₁ j₂ u.hom v.hom h).inv =
    TransverseDerivedBoundary.coneMap j₂ j₁ u.inv v.inv (inverse_square j₁ j₂ u v h) := by
  apply (cancel_epi (ConeDerivedComparison.coneIso j₁ j₂ u.hom v.hom h).hom).mp
  rw [Iso.hom_inv_id]
  simp only [ConeDerivedComparison.coneIso,asIso_hom,TransverseDerivedBoundary.coneMap,
    TransverseConeBoundary.coneMap,← Functor.map_comp,← mappingCone.map_comp,
    Iso.hom_inv_id,mappingCone.map_id,CategoryTheory.Functor.map_id]

#print axioms inverse_square
#print axioms inverse
end Verification.ConeDerivedInverse
