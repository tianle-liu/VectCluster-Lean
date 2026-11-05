/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrimeGlobalBoundary
import Verification.PrimeFlagProjection

/-!
# Prime Flag Boundary

The incident block of the actual global filtration is the positive
nested-cone boundary of the old/full flag inside one original J-chart.
Only canonical open excision and the proved cone projection enter.
-/
noncomputable section
namespace Verification.PrimeFlagBoundary
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.PrimeCoordinateFiltration Verification.PrimeLayerCover
open Verification.PrimeAdjacentExcision Verification.PrimeAdjacentAssembly
universe w
variable (A V : Type) [CommRing A] [Fintype V] [DecidableEq V]
variable (x : V → A) (Allowed : Finset V → Prop)
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (G : Scheme ⥤ CochainComplex C ℤ) (E : OpenConeExcision.StandardExcision G)
variable (hall : ∀ p : PrimeSpectrum A, Allowed (zeroSet x p))
variable (r : ℕ) (J : Index Allowed (r+1)) (v : J.val)
local notation "F" => PrimeLayerExcision.openChains A G

def rawProjection := TransverseConeBoundary.coneMap (rowArrow A V x J.val r G)
  (PrimeFlagProjection.firstArrow A V x J.val r J.property.1 v G)
  ((F).map (homOfLE (PrimeFlagOpens.previous_le_old A V x J.val r J.property.1 v))) (𝟙 _)
  (by simp only [rowArrow,OpenConeExcision.globalArrow,PrimeFlagProjection.firstArrow,
    Category.comp_id,← CategoryTheory.Functor.map_comp]; congr 1)

omit [HasDerivedCategory C] in
theorem raw_projection_boundary :
    NestedConeBoundary.boundary (rowArrow A V x J.val r G)
      (PrimeFlagProjection.secondArrow A V x J.val r G) ≫
        (rawProjection A V x Allowed G r J v)⟦(1 : ℤ)⟧' =
    NestedConeBoundary.boundary (PrimeFlagProjection.firstArrow A V x J.val r J.property.1 v G)
      (PrimeFlagProjection.secondArrow A V x J.val r G) := by
  have hi : mappingCone.inr (rowArrow A V x J.val r G) ≫ rawProjection A V x Allowed G r J v =
      mappingCone.inr (PrimeFlagProjection.firstArrow A V x J.val r J.property.1 v G) := by
    have ht := (mappingCone.triangleMap
      (rowArrow A V x J.val r G) (PrimeFlagProjection.firstArrow A V x J.val r J.property.1 v G)
      ((F).map (homOfLE (PrimeFlagOpens.previous_le_old A V x J.val r J.property.1 v))) (𝟙 _)
      (by simp only [rowArrow,OpenConeExcision.globalArrow,PrimeFlagProjection.firstArrow,
        Category.comp_id,← CategoryTheory.Functor.map_comp]; congr 1)).comm₂
    change mappingCone.inr (rowArrow A V x J.val r G) ≫ rawProjection A V x Allowed G r J v =
      (𝟙 _) ≫ mappingCone.inr (PrimeFlagProjection.firstArrow A V x J.val r J.property.1 v G) at ht
    simpa only [Category.id_comp] using ht
  simp only [NestedConeBoundary.boundary,Category.assoc,← CategoryTheory.Functor.map_comp,hi]

def boundary : PrimeLayerExcision.localRelative A V x Allowed G (r+1) J ⟶
    (PrimeFlagProjection.oldRelative A V x J.val r J.property.1 v G)⟦(1 : ℤ)⟧ :=
  DerivedCategory.Q.map (NestedConeBoundary.boundary
    (PrimeFlagProjection.firstArrow A V x J.val r J.property.1 v G)
    (PrimeFlagProjection.secondArrow A V x J.val r G)) ≫
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
        (mappingCone (PrimeFlagProjection.firstArrow A V x J.val r J.property.1 v G))

theorem projection_boundary :
    PrimeGlobalBoundary.localBoundary A V x Allowed G r J ≫
      (PrimeFlagProjection.projection A V x J.val r J.property.1 v G)⟦(1 : ℤ)⟧' =
        boundary A V x Allowed G r J v := by
  have hn := (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.naturality (rawProjection A V x Allowed G r J v)
  change DerivedCategory.Q.map ((rawProjection A V x Allowed G r J v)⟦(1 : ℤ)⟧') ≫ _ =
    _ ≫ (PrimeFlagProjection.projection A V x J.val r J.property.1 v G)⟦(1 : ℤ)⟧' at hn
  dsimp only [PrimeGlobalBoundary.localBoundary,boundary]
  rw [Category.assoc,← hn,← Category.assoc,← CategoryTheory.Functor.map_comp]
  congr 2
  exact raw_projection_boundary A V x Allowed G r J v

variable (herase : ∀ z : J.val, Allowed (J.val.erase z.val))

def targetIso : PrimeFlagProjection.oldRelative A V x J.val r J.property.1 v G ≅
    PrimeLayerExcision.localRelative A V x Allowed G r
      (edgeIndex V Allowed J.val r J.property.1 herase v) :=
  (PrimeFlagProjection.edgeFlagIso A V x J.val r J.property.1 v G E).symm ≪≫
    edgeIso A V x Allowed J.val r J.property.1 herase G v

theorem block_boundary :
    PrimeGlobalBoundary.block A V x Allowed G E hall r J
      (edgeIndex V Allowed J.val r J.property.1 herase v) =
        boundary A V x Allowed G r J v ≫ (targetIso A V x Allowed G E r J v herase).hom⟦(1 : ℤ)⟧' := by
  rw [PrimeGlobalBoundary.block_edge]
  dsimp only [targetIso,Iso.trans_hom,Iso.symm_hom]
  rw [← reassoc_of% (PrimeFlagProjection.projection_component A V x J.val r J.property.1 v G E)]
  simp only [CategoryTheory.Functor.map_comp,Category.assoc]
  rw [reassoc_of% (projection_boundary A V x Allowed G r J v)]

#print axioms rawProjection
#print axioms raw_projection_boundary
#print axioms boundary
#print axioms projection_boundary
#print axioms targetIso
#print axioms block_boundary
end Verification.PrimeFlagBoundary
