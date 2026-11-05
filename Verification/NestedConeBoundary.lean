/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.CoordinateFlag
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated

/-!
# Nested Cone Boundary

The support connecting map for a three-step flag is the positive cone
boundary of the map between the two old support cones. The comparison is
an actual mapping-cone homotopy equivalence, and the boundary identity is
proved before any geometric purity input.
-/
noncomputable section
namespace Verification.NestedConeBoundary
open CategoryTheory CategoryTheory.Limits CochainComplex
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C]
variable {U V W : CochainComplex C ℤ} (f : U ⟶ V) (g : V ⟶ W)

def supportMap : mappingCone f ⟶ mappingCone (f ≫ g) := (mappingConeCompTriangle f g).mor₁

def boundary : mappingCone g ⟶ (mappingCone f)⟦(1 : ℤ)⟧ :=
  TransverseConeBoundary.boundary g ≫ (mappingCone.inr f)⟦(1 : ℤ)⟧'

def coneEquiv : HomotopyEquiv (mappingCone g) (mappingCone (supportMap f g)) :=
  mappingConeCompHomotopyEquiv f g

theorem positive_boundary : (coneEquiv f g).hom ≫ TransverseConeBoundary.boundary (supportMap f g) =
    boundary f g := by
  have h := mappingConeCompHomotopyEquiv_comm₂ f g
  simpa only [coneEquiv,supportMap,TransverseConeBoundary.boundary,boundary,
    Preadditive.comp_neg,Preadditive.neg_comp,mappingConeCompTriangle_mor₃] using congrArg Neg.neg h

theorem naturality {U' V' W' : CochainComplex C ℤ} (f' : U' ⟶ V') (g' : V' ⟶ W')
    (u : U ⟶ U') (v : V ⟶ V') (w : W ⟶ W')
    (hf : f ≫ v = u ≫ f') (hg : g ≫ w = v ≫ g') :
    TransverseConeBoundary.coneMap g g' v w hg ≫ boundary f' g' =
      boundary f g ≫ (TransverseConeBoundary.coneMap f f' u v hf)⟦(1 : ℤ)⟧' := by
  have hi : mappingCone.inr f ≫ TransverseConeBoundary.coneMap f f' u v hf =
      v ≫ mappingCone.inr f' := (mappingCone.triangleMap f f' u v hf).comm₂
  simp only [boundary,← Category.assoc,TransverseConeBoundary.boundary_naturality]
  rw [Category.assoc,← CategoryTheory.Functor.map_comp,← hi,CategoryTheory.Functor.map_comp,Category.assoc]

variable [HasDerivedCategory.{w} C]

def derivedIso : DerivedCategory.Q.obj (mappingCone g) ≅
    DerivedCategory.Q.obj (mappingCone (supportMap f g)) :=
  asIso (DerivedCategory.Q.map (coneEquiv f g).hom)

theorem derived_positive_boundary : (derivedIso f g).hom ≫
    DerivedCategory.Q.map (TransverseConeBoundary.boundary (supportMap f g)) =
      DerivedCategory.Q.map (boundary f g) := by
  rw [derivedIso,asIso_hom,← CategoryTheory.Functor.map_comp,positive_boundary]

section Coordinates
variable (A ι : Type) [CommRing A] [Fintype ι] [DecidableEq ι] (x : ι → A) (v : ι)
variable (G : AlgebraicGeometry.Scheme ⥤ CochainComplex C ℤ)

def coordinateIso := derivedIso (CoordinateFlag.firstArrow A ι x v G) (CoordinateFlag.secondArrow A ι x G)

omit [Fintype ι] [DecidableEq ι] in
theorem coordinate_boundary : (coordinateIso A ι x v G).hom ≫
    DerivedCategory.Q.map (TransverseConeBoundary.boundary
      (supportMap (CoordinateFlag.firstArrow A ι x v G) (CoordinateFlag.secondArrow A ι x G))) =
    CoordinateFlag.boundary A ι x v G :=
  derived_positive_boundary _ _
end Coordinates

#print axioms supportMap
#print axioms boundary
#print axioms coneEquiv
#print axioms positive_boundary
#print axioms naturality
#print axioms derivedIso
#print axioms derived_positive_boundary
#print axioms coordinateIso
#print axioms coordinate_boundary
end Verification.NestedConeBoundary
