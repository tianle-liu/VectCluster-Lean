/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SplitEpiConeKernel

/-!
# Derived Cone Arrow

An ordinary arrow isomorphism in the derived category gives a comparison
of the actual cone triangles. Its positive-boundary formula is a theorem;
it is not additional naturality data imposed on a geometric differential.
-/
noncomputable section
namespace Verification.DerivedConeArrow
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CochainComplex
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable {U₁ W₁ U₂ W₂ : CochainComplex C ℤ}
variable (f : U₁ ⟶ W₁) (g : U₂ ⟶ W₂)
variable (u : DerivedCategory.Q.obj U₁ ≅ DerivedCategory.Q.obj U₂)
variable (v : DerivedCategory.Q.obj W₁ ≅ DerivedCategory.Q.obj W₂)
variable (square : DerivedCategory.Q.map f ≫ v.hom = u.hom ≫ DerivedCategory.Q.map g)

def triangleIso : DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle f) ≅
    DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle g) :=
  isoTriangleOfIso₁₂ _ _ (SplitEpiConeKernel.cone_distinguished f)
    (SplitEpiConeKernel.cone_distinguished g) u v square

def coneIso : DerivedCategory.Q.obj (mappingCone f) ≅ DerivedCategory.Q.obj (mappingCone g) :=
  Triangle.π₃.mapIso (triangleIso f g u v square)

def shiftedIso : DerivedCategory.Q.obj (U₁⟦(1 : ℤ)⟧) ≅ DerivedCategory.Q.obj (U₂⟦(1 : ℤ)⟧) :=
  (DerivedCategory.Q.commShiftIso (1 : ℤ)).app U₁ ≪≫
    (CategoryTheory.shiftFunctor (DerivedCategory C) (1 : ℤ)).mapIso u ≪≫
      ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app U₂).symm

theorem positive_boundary : (coneIso f g u v square).hom ≫ TransverseDerivedBoundary.boundary g =
    TransverseDerivedBoundary.boundary f ≫ (shiftedIso u).hom := by
  have h := (triangleIso f g u v square).hom.comm₃
  simp only [triangleIso, isoTriangleOfIso₁₂_hom_hom₁] at h
  change (DerivedCategory.Q.map (mappingCone.triangle f).mor₃ ≫
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app U₁) ≫ u.hom⟦(1 : ℤ)⟧' =
    (coneIso f g u v square).hom ≫ (DerivedCategory.Q.map (mappingCone.triangle g).mor₃ ≫
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app U₂) at h
  have hn := congrArg Neg.neg h
  simp only [TransverseDerivedBoundary.boundary,TransverseConeBoundary.boundary,
    Functor.map_neg,Preadditive.neg_comp,Preadditive.comp_neg] at hn ⊢
  apply (cancel_mono ((DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app U₂)).1
  dsimp only [shiftedIso,Iso.trans_hom,Iso.symm_hom,Functor.mapIso_hom]
  simpa only [Functor.comp_obj,Iso.app_hom,Iso.app_inv,Preadditive.neg_comp,Preadditive.comp_neg,Category.assoc,
    Iso.inv_hom_id_app_assoc,Iso.inv_hom_id_app,Iso.inv_hom_id,Category.comp_id] using hn.symm

#print axioms triangleIso
#print axioms coneIso
#print axioms shiftedIso
#print axioms positive_boundary
end Verification.DerivedConeArrow
