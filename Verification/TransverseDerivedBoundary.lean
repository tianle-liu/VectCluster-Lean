/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.TransverseConeBoundary
import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Transverse Derived Boundary

Purity comparisons belong in the actual derived category, not necessarily
as strict isomorphisms of chosen chain models. The cone boundary and its
naturality are localized by mathlib's real quasi-isomorphism localization.
-/
namespace Verification.TransverseDerivedBoundary
open CategoryTheory CategoryTheory.Limits CochainComplex
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C]
variable [HasDerivedCategory.{w} C]
variable {U₁ W₁ U₂ W₂ : CochainComplex C ℤ}
variable (j₁ : U₁ ⟶ W₁) (j₂ : U₂ ⟶ W₂)
variable (u : U₁ ⟶ U₂) (v : W₁ ⟶ W₂) (square : j₁ ≫ v = u ≫ j₂)

noncomputable def coneMap :
    DerivedCategory.Q.obj (mappingCone j₁) ⟶ DerivedCategory.Q.obj (mappingCone j₂) :=
  DerivedCategory.Q.map (Verification.TransverseConeBoundary.coneMap j₁ j₂ u v square)

noncomputable def boundary :
    DerivedCategory.Q.obj (mappingCone j₁) ⟶ DerivedCategory.Q.obj (U₁⟦(1 : ℤ)⟧) :=
  DerivedCategory.Q.map (Verification.TransverseConeBoundary.boundary j₁)

/-- Boundary naturality survives actual localization, with no new boundary hypothesis. -/
theorem boundary_naturality : coneMap j₁ j₂ u v square ≫ boundary j₂ =
    boundary j₁ ≫ DerivedCategory.Q.map (u⟦(1 : ℤ)⟧') := by
  simp only [coneMap, boundary, ← Functor.map_comp,
    Verification.TransverseConeBoundary.boundary_naturality]

variable {T₁ T₂ : DerivedCategory C}

noncomputable def thomBoundary (P : T₁ ≅ DerivedCategory.Q.obj (mappingCone j₁)) :
    T₁ ⟶ DerivedCategory.Q.obj (U₁⟦(1 : ℤ)⟧) := P.hom ≫ boundary j₁

/-- Only naturality of the standard purity comparison is an external input;
the adjacent boundary comparison is derived from it and the actual cone map. -/
theorem thom_naturality
    (P₁ : T₁ ≅ DerivedCategory.Q.obj (mappingCone j₁))
    (P₂ : T₂ ≅ DerivedCategory.Q.obj (mappingCone j₂)) (t : T₁ ⟶ T₂)
    (puritySquare : P₁.hom ≫ coneMap j₁ j₂ u v square = t ≫ P₂.hom) :
    t ≫ thomBoundary j₂ P₂ =
      thomBoundary j₁ P₁ ≫ DerivedCategory.Q.map (u⟦(1 : ℤ)⟧') := by
  simp only [thomBoundary, ← Category.assoc, ← puritySquare]
  rw [Category.assoc, boundary_naturality, ← Category.assoc]

/-- An actual derived isomorphism on closed Thom objects suffices; no strict
chain-level purity isomorphism is required. -/
theorem boundary_from_slice
    (P₁ : T₁ ≅ DerivedCategory.Q.obj (mappingCone j₁))
    (P₂ : T₂ ≅ DerivedCategory.Q.obj (mappingCone j₂)) (t : T₁ ≅ T₂)
    (puritySquare : P₁.hom ≫ coneMap j₁ j₂ u v square = t.hom ≫ P₂.hom) :
    thomBoundary j₂ P₂ =
      t.inv ≫ thomBoundary j₁ P₁ ≫ DerivedCategory.Q.map (u⟦(1 : ℤ)⟧') := by
  have hn := thom_naturality j₁ j₂ u v square P₁ P₂ t.hom puritySquare
  rw [← hn, ← Category.assoc, t.inv_hom_id, Category.id_comp]

#print axioms coneMap
#print axioms boundary
#print axioms boundary_naturality
#print axioms thomBoundary
#print axioms thom_naturality
#print axioms boundary_from_slice
end Verification.TransverseDerivedBoundary
