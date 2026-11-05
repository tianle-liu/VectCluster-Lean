/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.NestedConeBoundary
import Mathlib.AlgebraicGeometry.Restrict

/-!
# Open Flag Boundary

Restricting a genuine three-step open filtration to an actual chart
commutes with its support connecting map. This is proved from actual
mapping-cone naturality, before any support purity comparison is used.
-/
noncomputable section
namespace Verification.OpenFlagBoundary
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
universe u w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (X : Scheme.{u}) (F : X.Opens ⥤ CochainComplex C ℤ)
variable (U V W : X.Opens) (hUV : U ≤ V) (hVW : V ≤ W)
variable (Z : X.Opens) (hZW : Z ≤ W)

def firstArrow : F.obj U ⟶ F.obj V := F.map (homOfLE hUV)
def secondArrow : F.obj V ⟶ F.obj W := F.map (homOfLE hVW)
def localFirst : F.obj (U ⊓ Z) ⟶ F.obj (V ⊓ Z) := F.map (homOfLE (inf_le_inf_right Z hUV))
def localSecond : F.obj (V ⊓ Z) ⟶ F.obj Z := F.map (homOfLE inf_le_right)

omit [HasBinaryBiproducts C] [HasDerivedCategory C] in
theorem first_square : localFirst X F U V hUV Z ≫ F.map (homOfLE inf_le_left) =
    F.map (homOfLE inf_le_left) ≫ firstArrow X F U V hUV := by
  simp only [localFirst,firstArrow,← CategoryTheory.Functor.map_comp]
  congr 1

omit [HasBinaryBiproducts C] [HasDerivedCategory C] in
theorem second_square : localSecond X F V Z ≫ F.map (homOfLE hZW) =
    F.map (homOfLE inf_le_left) ≫ secondArrow X F V W hVW := by
  simp only [localSecond,secondArrow,← CategoryTheory.Functor.map_comp]
  congr 1

def sourceMap := TransverseConeBoundary.coneMap (localSecond X F V Z) (secondArrow X F V W hVW)
  (F.map (homOfLE inf_le_left)) (F.map (homOfLE hZW)) (second_square X F V W hVW Z hZW)

def rowMap := TransverseConeBoundary.coneMap (localFirst X F U V hUV Z) (firstArrow X F U V hUV)
  (F.map (homOfLE inf_le_left)) (F.map (homOfLE inf_le_left)) (first_square X F U V hUV Z)

omit [HasDerivedCategory C] in
theorem boundary_naturality : sourceMap X F V W hVW Z hZW ≫
    NestedConeBoundary.boundary (firstArrow X F U V hUV) (secondArrow X F V W hVW) =
      NestedConeBoundary.boundary (localFirst X F U V hUV Z) (localSecond X F V Z) ≫
        (rowMap X F U V hUV Z)⟦(1 : ℤ)⟧' :=
  NestedConeBoundary.naturality _ _ _ _ _ _ _ _ _

theorem derived_boundary_naturality : DerivedCategory.Q.map (sourceMap X F V W hVW Z hZW) ≫
    DerivedCategory.Q.map (NestedConeBoundary.boundary (firstArrow X F U V hUV) (secondArrow X F V W hVW)) =
      DerivedCategory.Q.map (NestedConeBoundary.boundary (localFirst X F U V hUV Z) (localSecond X F V Z)) ≫
        DerivedCategory.Q.map ((rowMap X F U V hUV Z)⟦(1 : ℤ)⟧') := by
  simp only [← CategoryTheory.Functor.map_comp,boundary_naturality]

#print axioms firstArrow
#print axioms secondArrow
#print axioms localFirst
#print axioms localSecond
#print axioms first_square
#print axioms second_square
#print axioms sourceMap
#print axioms rowMap
#print axioms boundary_naturality
#print axioms derived_boundary_naturality
end Verification.OpenFlagBoundary
