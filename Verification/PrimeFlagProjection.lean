/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrimeFlagOpens
import Verification.PrimeAdjacentProjection
import Verification.ConeFactorThroughIdentity
import Verification.OpenOneExcision

/-!
# Prime Flag Projection

The projection of the previous layer to J minus v is the literal map
of cone pairs obtained by enlarging the old open set. Excision identifies
its target with that face's local cone. Every other edge factors through
an identity cone, hence vanishes in the actual derived category.
-/
set_option maxHeartbeats 80000
noncomputable section
namespace Verification.PrimeFlagProjection
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.PrimeCoordinateFiltration Verification.PrimeAdjacentExcision
universe w
variable (A V : Type) [CommRing A] [Fintype V] [DecidableEq V]
variable (x : V → A) (J : Finset V) (r : ℕ) (hr : J.card = r+1) (v : J)
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (G : Scheme ⥤ CochainComplex C ℤ) (E : OpenConeExcision.StandardExcision G)
local notation "F" => PrimeLayerExcision.openChains A G

def firstArrow := (F).map (homOfLE (PrimeFlagOpens.old_le_current A V x J r hr v))
def secondArrow := (F).map (homOfLE (inf_le_right : current A V x J r ≤ openBy x J))
def oldRelative := DerivedCategory.Q.obj (mappingCone (firstArrow A V x J r hr v G))

def projection : DerivedCategory.Q.obj (mappingCone (rowArrow A V x J r G)) ⟶
    oldRelative A V x J r hr v G :=
  TransverseDerivedBoundary.coneMap _ _
    ((F).map (homOfLE (PrimeFlagOpens.previous_le_old A V x J r hr v))) (𝟙 _)
    (by simp only [rowArrow, OpenConeExcision.globalArrow, firstArrow, Category.comp_id,
      ← CategoryTheory.Functor.map_comp]; congr 1)

def edgeOldIso : edgeCone A V x J r G v ≅
    OpenConeExcision.localCone (Spec (CommRingCat.of A)) F (PrimeFlagOpens.old A V x J v)
      (fun _ : PUnit => edgeChart A V x J v) PUnit.unit :=
  ConeDerivedComparison.coneIso _ _
    ((F).map (eqToHom (PrimeFlagOpens.old_inter_edge A V x J r hr v).symm)) (𝟙 _)
    (by simp only [OpenConeExcision.localArrow,Category.comp_id,← CategoryTheory.Functor.map_comp]; congr 1)

def edgeFlagIso : edgeCone A V x J r G v ≅ oldRelative A V x J r hr v G :=
  edgeOldIso A V x J r hr v G ≪≫
    OpenOneExcision.relativeIso G E (Spec (CommRingCat.of A))
      (PrimeFlagOpens.old A V x J v) (current A V x J r)
      (PrimeFlagOpens.old_le_current A V x J r hr v) (edgeChart A V x J v)
      (edgeChart_le_current A V x J r hr v) (PrimeFlagOpens.cover A V x J r hr v)

theorem edge_projection :
    biproduct.ι (edgeCone A V x J r G) v ≫ assembly A V x J r hr G ≫
      projection A V x J r hr v G = (edgeFlagIso A V x J r hr v G E).hom := by
  simp only [assembly,OpenConeExcision.assembly,biproduct.ι_desc_assoc,
    OpenConeExcision.localMap,projection,edgeFlagIso,Iso.trans_hom,edgeOldIso,
    OpenOneExcision.relativeIso,OpenOneExcision.localMap,ConeDerivedComparison.coneIso,
    asIso_hom,TransverseDerivedBoundary.coneMap,TransverseConeBoundary.coneMap,
    rowArrow, OpenConeExcision.globalArrow, OpenConeExcision.localArrow, firstArrow,
    ← CategoryTheory.Functor.map_comp,← mappingCone.map_comp]
  congr 1
  change _ = mappingCone.map _
    (OpenConeExcision.localArrow (Spec (CommRingCat.of A)) F (PrimeFlagOpens.old A V x J v)
      (fun _ : PUnit => edgeChart A V x J v) PUnit.unit) _ _ _ ≫
    mappingCone.map (OpenConeExcision.localArrow (Spec (CommRingCat.of A)) F
      (PrimeFlagOpens.old A V x J v) (fun _ : PUnit => edgeChart A V x J v) PUnit.unit) _ _ _ _
  rw [← mappingCone.map_comp]
  simp only [Category.comp_id,Category.id_comp,← CategoryTheory.Functor.map_comp]
  congr 1
  change (F).map _ = (F).map _ ≫ (F).map _
  rw [← CategoryTheory.Functor.map_comp]
  congr 1

theorem other_projection (z : J) (hz : z ≠ v) :
    biproduct.ι (edgeCone A V x J r G) z ≫ assembly A V x J r hr G ≫
      projection A V x J r hr v G = 0 := by
  simp only [assembly,OpenConeExcision.assembly,biproduct.ι_desc_assoc,
    OpenConeExcision.localMap,projection,TransverseDerivedBoundary.coneMap,
    TransverseConeBoundary.coneMap,rowArrow, OpenConeExcision.globalArrow, OpenConeExcision.localArrow, firstArrow,
    ← CategoryTheory.Functor.map_comp,← mappingCone.map_comp]
  apply ConeFactorThroughIdentity.map_zero _ _ _ _ _
    ((F).map (homOfLE (PrimeFlagOpens.other_le_old A V x J v z hz)))
  · simp only [OpenConeExcision.localArrow,← CategoryTheory.Functor.map_comp]
    congr 1
  · simp only [firstArrow,Category.comp_id,← CategoryTheory.Functor.map_comp]
    congr 1

theorem projection_matrix :
    (PrimeAdjacentExcision.relativeIso A V x J r hr G E).hom ≫ projection A V x J r hr v G =
      biproduct.π (edgeCone A V x J r G) v ≫ (edgeFlagIso A V x J r hr v G E).hom := by
  apply biproduct.hom_ext'
  intro z
  by_cases h : z=v
  · subst z
    rw [biproduct.ι_π_self_assoc]
    exact edge_projection A V x J r hr v G E
  · rw [biproduct.ι_π_ne_assoc _ h,zero_comp]
    exact other_projection A V x J r hr v G z h

theorem projection_component :
    projection A V x J r hr v G ≫ (edgeFlagIso A V x J r hr v G E).inv =
      (PrimeAdjacentExcision.relativeIso A V x J r hr G E).inv ≫
        biproduct.π (edgeCone A V x J r G) v := by
  apply (cancel_epi (PrimeAdjacentExcision.relativeIso A V x J r hr G E).hom).1
  rw [Iso.hom_inv_id_assoc,← Category.assoc,projection_matrix]
  simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]

#print axioms firstArrow
#print axioms secondArrow
#print axioms oldRelative
#print axioms projection
#print axioms edgeOldIso
#print axioms edgeFlagIso
#print axioms edge_projection
#print axioms other_projection
#print axioms projection_matrix
#print axioms projection_component
end Verification.PrimeFlagProjection
