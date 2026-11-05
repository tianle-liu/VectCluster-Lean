/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-!
# Transverse Cone Boundary

Boundary transport through an actual map of localization cones. The boundary
is constructed from mathlib's mapping cone, not given as an arbitrary map.
The only later purity input is a comparison of the cones with Thom objects;
its naturality does not assume the desired boundary formula.
-/
namespace Verification.TransverseConeBoundary
open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ZeroObject
variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
variable {U₁ W₁ U₂ W₂ : CochainComplex C ℤ}
variable (j₁ : U₁ ⟶ W₁) (j₂ : U₂ ⟶ W₂)
variable (u : U₁ ⟶ U₂) (w : W₁ ⟶ W₂) (square : j₁ ≫ w = u ≫ j₂)

/-- The literal cone map of the supplied commuting open/ambient square. -/
noncomputable def coneMap : mappingCone j₁ ⟶ mappingCone j₂ :=
  mappingCone.map j₁ j₂ u w square

/-- Positive projection convention on the shifted open summand, matching the
left-residue orientation. Mathlib's standard triangle has its negative. -/
noncomputable def boundary : mappingCone j₁ ⟶ U₁⟦(1 : ℤ)⟧ :=
  -(mappingCone.triangle j₁).mor₃

/-- Its coefficient on the shifted open factor is +1, with the canonical shift identification. -/
theorem boundary_left (p q : ℤ) (hpq : p + (-1) = q) :
    (mappingCone.inl j₁).v p q hpq ≫ (boundary j₁).f q =
      (U₁.shiftFunctorObjXIso 1 q p (by omega)).inv := by
  change (mappingCone.inl j₁).v p q hpq ≫ (-(mappingCone.triangle j₁).mor₃.f q) = _
  rw [Preadditive.comp_neg, mappingCone.inl_v_triangle_mor₃_f, neg_neg]

/-- The ambient summand has zero boundary. -/
theorem boundary_right (p : ℤ) : (mappingCone.inr j₁).f p ≫ (boundary j₁).f p = 0 := by
  simp [boundary]

/-- Naturality is proved for the actual constructed cones and boundary maps. -/
theorem boundary_naturality : coneMap j₁ j₂ u w square ≫ boundary j₂ =
    boundary j₁ ≫ u⟦(1 : ℤ)⟧' := by
  have hn := (mappingCone.triangleMap j₁ j₂ u w square).comm₃.symm
  change coneMap j₁ j₂ u w square ≫ (mappingCone.triangle j₂).mor₃ =
    (mappingCone.triangle j₁).mor₃ ≫ u⟦(1 : ℤ)⟧' at hn
  simp only [boundary, Preadditive.comp_neg, Preadditive.neg_comp, hn]

variable {T₁ T₂ : CochainComplex C ℤ}

/-- The boundary on a Thom model is the explicitly transported cone boundary. -/
noncomputable def thomBoundary (purity : T₁ ≅ mappingCone j₁) : T₁ ⟶ U₁⟦(1 : ℤ)⟧ :=
  purity.hom ≫ boundary j₁

/-- Standard purity naturality is a square of Thom/cone comparisons. The
adjacent boundary square is then a theorem, not an input. -/
theorem thom_naturality (P₁ : T₁ ≅ mappingCone j₁) (P₂ : T₂ ≅ mappingCone j₂)
    (t : T₁ ⟶ T₂)
    (puritySquare : P₁.hom ≫ coneMap j₁ j₂ u w square = t ≫ P₂.hom) :
    t ≫ thomBoundary j₂ P₂ = thomBoundary j₁ P₁ ≫ u⟦(1 : ℤ)⟧' := by
  simp only [thomBoundary, ← Category.assoc, ← puritySquare]
  rw [Category.assoc, boundary_naturality, ← Category.assoc]

/-- When the actual closed-stratum comparison is an isomorphism, the target
boundary is computed entirely on the transverse slice and its actual open map. -/
theorem boundary_from_slice (P₁ : T₁ ≅ mappingCone j₁) (P₂ : T₂ ≅ mappingCone j₂)
    (t : T₁ ≅ T₂)
    (puritySquare : P₁.hom ≫ coneMap j₁ j₂ u w square = t.hom ≫ P₂.hom) :
    thomBoundary j₂ P₂ = t.inv ≫ thomBoundary j₁ P₁ ≫ u⟦(1 : ℤ)⟧' := by
  have hn := thom_naturality j₁ j₂ u w square P₁ P₂ t.hom puritySquare
  rw [← hn, ← Category.assoc, t.inv_hom_id, Category.id_comp]

#print axioms coneMap
#print axioms boundary
#print axioms boundary_left
#print axioms boundary_right
#print axioms boundary_naturality
#print axioms thomBoundary
#print axioms thom_naturality
#print axioms boundary_from_slice
end Verification.TransverseConeBoundary
