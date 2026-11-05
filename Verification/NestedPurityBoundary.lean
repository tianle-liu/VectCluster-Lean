/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.NestedConeBoundary
import Verification.DerivedConeArrow

/-!
# Nested Purity Boundary

A purity comparison of the ordinary old-support arrow determines the
adjacent boundary of a flag. The conclusion is derived from the actual
nested mapping-cone homotopy equivalence and distinguished triangles.
-/
noncomputable section
namespace Verification.NestedPurityBoundary
open CategoryTheory CategoryTheory.Limits CochainComplex
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable {U V W P Q : CochainComplex C ℤ}
variable (f : U ⟶ V) (g : V ⟶ W) (h : P ⟶ Q)
variable (u : DerivedCategory.Q.obj (mappingCone f) ≅ DerivedCategory.Q.obj P)
variable (v : DerivedCategory.Q.obj (mappingCone (f ≫ g)) ≅ DerivedCategory.Q.obj Q)
variable (ordinarySquare : DerivedCategory.Q.map (NestedConeBoundary.supportMap f g) ≫ v.hom =
    u.hom ≫ DerivedCategory.Q.map h)

def coneIso : DerivedCategory.Q.obj (mappingCone g) ≅ DerivedCategory.Q.obj (mappingCone h) :=
  NestedConeBoundary.derivedIso f g ≪≫
    DerivedConeArrow.coneIso (NestedConeBoundary.supportMap f g) h u v ordinarySquare

theorem positive_boundary : (coneIso f g h u v ordinarySquare).hom ≫
    TransverseDerivedBoundary.boundary h =
      DerivedCategory.Q.map (NestedConeBoundary.boundary f g) ≫ (DerivedConeArrow.shiftedIso u).hom := by
  simp only [coneIso,Iso.trans_hom,Category.assoc,DerivedConeArrow.positive_boundary]
  rw [← Category.assoc,TransverseDerivedBoundary.boundary,NestedConeBoundary.derived_positive_boundary]

section ActualFlag
variable (A ι : Type) [CommRing A] [Fintype ι] [DecidableEq ι] (x : ι → A) (a : ι)
variable (G : AlgebraicGeometry.Scheme ⥤ CochainComplex C ℤ)
variable (u₀ : DerivedCategory.Q.obj (mappingCone (CoordinateFlag.firstArrow A ι x a G)) ≅ DerivedCategory.Q.obj P)
variable (v₀ : DerivedCategory.Q.obj (mappingCone (CoordinateFlag.firstArrow A ι x a G ≫
    CoordinateFlag.secondArrow A ι x G)) ≅ DerivedCategory.Q.obj Q)
variable (square₀ : DerivedCategory.Q.map (NestedConeBoundary.supportMap
    (CoordinateFlag.firstArrow A ι x a G) (CoordinateFlag.secondArrow A ι x G)) ≫ v₀.hom =
      u₀.hom ≫ DerivedCategory.Q.map h)

def coordinateIso := coneIso (CoordinateFlag.firstArrow A ι x a G)
  (CoordinateFlag.secondArrow A ι x G) h u₀ v₀ square₀

omit [Fintype ι] [DecidableEq ι] in
theorem coordinate_boundary : (coordinateIso h A ι x a G u₀ v₀ square₀).hom ≫
    TransverseDerivedBoundary.boundary h =
      CoordinateFlag.boundary A ι x a G ≫ (DerivedConeArrow.shiftedIso u₀).hom :=
  positive_boundary _ _ _ _ _ _
end ActualFlag

#print axioms coneIso
#print axioms positive_boundary
#print axioms coordinateIso
#print axioms coordinate_boundary
end Verification.NestedPurityBoundary
