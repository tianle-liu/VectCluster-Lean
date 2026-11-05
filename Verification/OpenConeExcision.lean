/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.TransverseDerivedBoundary
import Mathlib.AlgebraicGeometry.Restrict

/-!
# Open Cone Excision

The standard excision input is uniform on actual scheme opens. Its map
is the canonical sum of maps of literal localization cones. It does not
postulate a cellular differential or any exchange-specific identification.
-/
noncomputable section
namespace Verification.OpenConeExcision
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
universe u w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (X : Scheme.{u}) (F : X.Opens ⥤ CochainComplex C ℤ)
variable (U V : X.Opens) (hUV : U ≤ V)
variable {ι : Type u} [Fintype ι] (W : ι → X.Opens) (hW : ∀ i, W i ≤ V)

def globalArrow : F.obj U ⟶ F.obj V := F.map (homOfLE hUV)

def localArrow (i : ι) : F.obj (U ⊓ W i) ⟶ F.obj (W i) := F.map (homOfLE inf_le_right)

omit [HasBinaryBiproducts C] [HasDerivedCategory C] [Fintype ι] in
theorem local_square (i : ι) : localArrow X F U W i ≫ F.map (homOfLE (hW i)) =
    F.map (homOfLE inf_le_left) ≫ globalArrow X F U V hUV := by
  simp only [localArrow,globalArrow,← CategoryTheory.Functor.map_comp]
  congr 1

def localCone (i : ι) : DerivedCategory C := DerivedCategory.Q.obj (mappingCone (localArrow X F U W i))

def localMap (i : ι) : localCone X F U W i ⟶ DerivedCategory.Q.obj (mappingCone (globalArrow X F U V hUV)) :=
  TransverseDerivedBoundary.coneMap _ _ (F.map (homOfLE inf_le_left))
    (F.map (homOfLE (hW i))) (local_square X F U V hUV W hW i)

def assembly : (⨁ fun i => localCone X F U W i) ⟶
    DerivedCategory.Q.obj (mappingCone (globalArrow X F U V hUV)) :=
  biproduct.desc (localMap X F U V hUV W hW)

theorem assembly_inclusion (i : ι) : biproduct.ι (localCone X F U W) i ≫
    assembly X F U V hUV W hW = localMap X F U V hUV W hW i := biproduct.ι_desc _ _

omit [Fintype ι] in
theorem local_boundary (i : ι) : localMap X F U V hUV W hW i ≫
    TransverseDerivedBoundary.boundary (globalArrow X F U V hUV) =
      TransverseDerivedBoundary.boundary (localArrow X F U W i) ≫
        DerivedCategory.Q.map ((F.map (homOfLE inf_le_left))⟦(1 : ℤ)⟧') :=
  TransverseDerivedBoundary.boundary_naturality _ _ _ _ _

variable (G : Scheme.{u} ⥤ CochainComplex C ℤ)

/-- Uniform finite excision for a chains theory. All conditions are actual
open-subscheme containment, covering, and disjointness outside U. -/
structure StandardExcision where
  isIso_assembly : ∀ (X : Scheme.{u}) (U V : X.Opens) (hUV : U ≤ V)
    (ι : Type u) [Fintype ι] (W : ι → X.Opens) (hW : ∀ i, W i ≤ V),
    V ≤ U ⊔ ⨆ i, W i → (∀ i j, i ≠ j → W i ⊓ W j ≤ U) →
    IsIso (assembly X (X.restrictFunctor ⋙ Over.forget X ⋙ G) U V hUV W hW)

#print axioms globalArrow
#print axioms localArrow
#print axioms local_square
#print axioms localCone
#print axioms localMap
#print axioms assembly
#print axioms assembly_inclusion
#print axioms local_boundary
#print axioms StandardExcision
end Verification.OpenConeExcision
