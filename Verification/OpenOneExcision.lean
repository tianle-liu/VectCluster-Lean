/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OpenConeExcision

/-!
# Open One Excision

The single-open case of finite excision is the canonical map of actual
localization cones, and retains its positive boundary.
-/
noncomputable section
namespace Verification.OpenOneExcision
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (G : Scheme ⥤ CochainComplex C ℤ) (E : OpenConeExcision.StandardExcision G)
variable (X : Scheme) (U V : X.Opens) (hUV : U ≤ V) (Z : X.Opens) (hZ : Z ≤ V)
local notation "F" => X.restrictFunctor ⋙ Over.forget X ⋙ G

def singletonIso (D : DerivedCategory C) : D ≅ ⨁ (fun _ : PUnit => D) where
  hom := biproduct.ι (fun _ : PUnit => D) PUnit.unit
  inv := biproduct.π (fun _ : PUnit => D) PUnit.unit
  hom_inv_id := by simp
  inv_hom_id := by
    apply biproduct.hom_ext'
    intro i
    cases i
    simp

def localMap := OpenConeExcision.localMap X F U V hUV (fun _ : PUnit => Z) (fun _ => hZ) PUnit.unit

include E in
theorem localMap_isIso (hcover : V ≤ U ⊔ Z) : IsIso (localMap G X U V hUV Z hZ) := by
  letI := E.isIso_assembly X U V hUV PUnit (fun _ => Z) (fun _ => hZ)
    (by simpa only [iSup_const] using hcover)
    (fun i j h => (h (Subsingleton.elim i j)).elim)
  have h : localMap G X U V hUV Z hZ =
      (singletonIso (OpenConeExcision.localCone X F U (fun _ : PUnit => Z) PUnit.unit)).hom ≫
        OpenConeExcision.assembly X F U V hUV (fun _ : PUnit => Z) (fun _ => hZ) := by
    exact (OpenConeExcision.assembly_inclusion X F U V hUV (fun _ : PUnit => Z) (fun _ => hZ) PUnit.unit).symm
  rw [h]
  infer_instance

def relativeIso (hcover : V ≤ U ⊔ Z) :
    OpenConeExcision.localCone X F U (fun _ : PUnit => Z) PUnit.unit ≅
      DerivedCategory.Q.obj (mappingCone (OpenConeExcision.globalArrow X F U V hUV)) := by
  letI := localMap_isIso G E X U V hUV Z hZ hcover
  exact asIso (localMap G X U V hUV Z hZ)

theorem relativeIso_boundary (hcover : V ≤ U ⊔ Z) : (relativeIso G E X U V hUV Z hZ hcover).hom ≫
    TransverseDerivedBoundary.boundary (OpenConeExcision.globalArrow X F U V hUV) =
      TransverseDerivedBoundary.boundary (OpenConeExcision.localArrow X F U (fun _ : PUnit => Z) PUnit.unit) ≫
        DerivedCategory.Q.map (((F).map (homOfLE (inf_le_left : U ⊓ Z ≤ U)))⟦(1 : ℤ)⟧') :=
  OpenConeExcision.local_boundary X F U V hUV (fun _ : PUnit => Z) (fun _ => hZ) PUnit.unit

#print axioms singletonIso
#print axioms localMap
#print axioms localMap_isIso
#print axioms relativeIso
#print axioms relativeIso_boundary
end Verification.OpenOneExcision
