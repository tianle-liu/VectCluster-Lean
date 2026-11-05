/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.TransverseDerivedBoundary

/-!
# Cone Derived Comparison

A commuting square whose two vertical maps are derived isomorphisms
induces an actual derived isomorphism of its mapping cones. The comparison
retains the positive boundary map, including its sign.
-/
namespace Verification.ConeDerivedComparison
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CochainComplex
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C]
variable [HasDerivedCategory.{w} C]
variable {U₁ W₁ U₂ W₂ : CochainComplex C ℤ}
variable (j₁ : U₁ ⟶ W₁) (j₂ : U₂ ⟶ W₂)
variable (u : U₁ ⟶ U₂) (v : W₁ ⟶ W₂) (square : j₁ ≫ v = u ≫ j₂)
variable [IsIso (DerivedCategory.Q.map u)] [IsIso (DerivedCategory.Q.map v)]

theorem coneMap_isIso : IsIso (TransverseDerivedBoundary.coneMap j₁ j₂ u v square) := by
  let m := DerivedCategory.Q.mapTriangle.map (mappingCone.triangleMap j₁ j₂ u v square)
  have h₁ : IsIso m.hom₁ := inferInstanceAs (IsIso (DerivedCategory.Q.map u))
  have h₂ : IsIso m.hom₂ := inferInstanceAs (IsIso (DerivedCategory.Q.map v))
  exact isIso₃_of_isIso₁₂ m
    ((DerivedCategory.mem_distTriang_iff _).mpr ⟨_, _, j₁, ⟨Iso.refl _⟩⟩)
    ((DerivedCategory.mem_distTriang_iff _).mpr ⟨_, _, j₂, ⟨Iso.refl _⟩⟩) h₁ h₂

noncomputable def coneIso :
    DerivedCategory.Q.obj (mappingCone j₁) ≅ DerivedCategory.Q.obj (mappingCone j₂) := by
  letI := coneMap_isIso j₁ j₂ u v square
  exact asIso (TransverseDerivedBoundary.coneMap j₁ j₂ u v square)

theorem coneIso_boundary : (coneIso j₁ j₂ u v square).hom ≫
    TransverseDerivedBoundary.boundary j₂ =
      TransverseDerivedBoundary.boundary j₁ ≫ DerivedCategory.Q.map (u⟦(1 : ℤ)⟧') :=
  TransverseDerivedBoundary.boundary_naturality j₁ j₂ u v square

#print axioms coneMap_isIso
#print axioms coneIso
#print axioms coneIso_boundary
end Verification.ConeDerivedComparison
