/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ConeDerivedComparison
import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Localized Cone Comparison

A square of actual raw chain maps becomes a cone isomorphism when its
vertical maps are inverted by the ambient triangulated localization.
Ordinary derived invertibility is not assumed.
-/
noncomputable section
namespace Verification.LocalizedConeComparison
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CochainComplex
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
variable [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]
variable (L : DerivedCategory C ⥤ D) [L.CommShift ℤ] [L.IsTriangulated]
variable {U₁ W₁ U₂ W₂ : CochainComplex C ℤ}
variable (j₁ : U₁ ⟶ W₁) (j₂ : U₂ ⟶ W₂)
variable (u : U₁ ⟶ U₂) (v : W₁ ⟶ W₂) (square : j₁ ≫ v = u ≫ j₂)
variable [IsIso (L.map (DerivedCategory.Q.map u))] [IsIso (L.map (DerivedCategory.Q.map v))]

theorem coneMap_isIso : IsIso (L.map (TransverseDerivedBoundary.coneMap j₁ j₂ u v square)) := by
  let m := L.mapTriangle.map (DerivedCategory.Q.mapTriangle.map (mappingCone.triangleMap j₁ j₂ u v square))
  have h₁ : IsIso m.hom₁ := inferInstanceAs (IsIso (L.map (DerivedCategory.Q.map u)))
  have h₂ : IsIso m.hom₂ := inferInstanceAs (IsIso (L.map (DerivedCategory.Q.map v)))
  exact isIso₃_of_isIso₁₂ m
    (L.map_distinguished _ ((DerivedCategory.mem_distTriang_iff _).mpr ⟨_,_,j₁,⟨Iso.refl _⟩⟩))
    (L.map_distinguished _ ((DerivedCategory.mem_distTriang_iff _).mpr ⟨_,_,j₂,⟨Iso.refl _⟩⟩)) h₁ h₂

def coneIso : L.obj (DerivedCategory.Q.obj (mappingCone j₁)) ≅
    L.obj (DerivedCategory.Q.obj (mappingCone j₂)) := by
  letI := coneMap_isIso L j₁ j₂ u v square
  exact asIso (L.map (TransverseDerivedBoundary.coneMap j₁ j₂ u v square))

theorem coneIso_boundary : (coneIso L j₁ j₂ u v square).hom ≫
    L.map (TransverseDerivedBoundary.boundary j₂) =
      L.map (TransverseDerivedBoundary.boundary j₁) ≫ L.map (DerivedCategory.Q.map (u⟦(1 : ℤ)⟧')) := by
  change L.map _ ≫ L.map _ = _
  rw [← Functor.map_comp, TransverseDerivedBoundary.boundary_naturality, Functor.map_comp]

#print axioms coneMap_isIso
#print axioms coneIso
#print axioms coneIso_boundary
end Verification.LocalizedConeComparison
