/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrimeFlagBoundary
import Verification.PrimeFlagPair
import Verification.PrimeCanonicalCone

/-!
# Prime Coordinate Flag Boundary

The incident global component is the literal coordinate-flag boundary
on the actual localized coordinate chart. The comparison uses explicit
isomorphisms of all three open schemes and canonical cone maps.
-/
noncomputable section
namespace Verification.PrimeCoordinateFlagBoundary
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.PrimeCoordinateFiltration Verification.PrimeLayerCover
open Verification.PrimeLocalPair
universe w
variable (A V : Type) [CommRing A] [Fintype V] [DecidableEq V]
variable (x : V → A) (Allowed : Finset V → Prop)
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (G : Scheme ⥤ CochainComplex C ℤ) (E : OpenConeExcision.StandardExcision G)
variable (hall : ∀ p : PrimeSpectrum A, Allowed (zeroSet x p))
variable (r : ℕ) (J : Index Allowed (r+1)) (v : J.val)
local notation "S" => OpenRing A V x J.val
local notation "y" => coordinate A V x J.val

omit [HasBinaryBiproducts C] [HasDerivedCategory C] in
theorem first_square :
    CoordinateFlag.firstArrow S J.val y v G ≫ G.map (PrimeFlagPair.fullIso A V x J.val r J.property.1).hom =
      G.map (PrimeFlagPair.oldIso A V x J.val r J.property.1 v).hom ≫
        PrimeFlagProjection.firstArrow A V x J.val r J.property.1 v G := by
  change G.map _ ≫ G.map _ = G.map _ ≫ G.map _
  rw [← CategoryTheory.Functor.map_comp,← CategoryTheory.Functor.map_comp]
  exact congrArg G.map (PrimeFlagPair.old_square A V x J.val r J.property.1 v)

omit [HasBinaryBiproducts C] [HasDerivedCategory C] in
theorem second_square :
    CoordinateFlag.secondArrow S J.val y G ≫ G.map (ambientIso A V x J.val).hom =
      G.map (PrimeFlagPair.fullIso A V x J.val r J.property.1).hom ≫
        PrimeFlagProjection.secondArrow A V x J.val r G := by
  change G.map _ ≫ G.map _ = G.map _ ≫ G.map _
  rw [← CategoryTheory.Functor.map_comp,← CategoryTheory.Functor.map_comp]
  exact congrArg G.map (PrimeFlagPair.full_square A V x J.val r J.property.1)

def oldIso : CoordinateFlag.oldRelative S J.val y v G ≅
    PrimeFlagProjection.oldRelative A V x J.val r J.property.1 v G :=
  ConeDerivedComparison.coneIso _ _
    (G.map (PrimeFlagPair.oldIso A V x J.val r J.property.1 v).hom)
    (G.map (PrimeFlagPair.fullIso A V x J.val r J.property.1).hom)
    (first_square A V x Allowed G r J v)

def fullIso : CoordinateFlag.fullRelative S J.val y G ≅
    PrimeLayerExcision.localRelative A V x Allowed G (r+1) J :=
  ConeDerivedComparison.coneIso _ _
    (G.map (PrimeFlagPair.fullIso A V x J.val r J.property.1).hom)
    (G.map (ambientIso A V x J.val).hom)
    (second_square A V x Allowed G r J)

theorem fullIso_eq_layerIso : fullIso A V x Allowed G r J =
    PrimeLocalCone.layerIso A V x G Allowed (r+1) J := by
  rw [← PrimeCanonicalCone.relativeIso_eq]
  rfl

theorem positive_boundary :
    (fullIso A V x Allowed G r J).hom ≫ PrimeFlagBoundary.boundary A V x Allowed G r J v =
      CoordinateFlag.boundary S J.val y v G ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (mappingCone (CoordinateFlag.firstArrow S J.val y v G)) ≫
          (oldIso A V x Allowed G r J v).hom⟦(1 : ℤ)⟧' := by
  have h := NestedConeBoundary.naturality
    (CoordinateFlag.firstArrow S J.val y v G) (CoordinateFlag.secondArrow S J.val y G)
    (PrimeFlagProjection.firstArrow A V x J.val r J.property.1 v G)
    (PrimeFlagProjection.secondArrow A V x J.val r G)
    (G.map (PrimeFlagPair.oldIso A V x J.val r J.property.1 v).hom)
    (G.map (PrimeFlagPair.fullIso A V x J.val r J.property.1).hom)
    (G.map (ambientIso A V x J.val).hom)
    (first_square A V x Allowed G r J v) (second_square A V x Allowed G r J)
  have hh := congrArg DerivedCategory.Q.map h
  simp only [CategoryTheory.Functor.map_comp] at hh
  change (fullIso A V x Allowed G r J).hom ≫ DerivedCategory.Q.map
    (NestedConeBoundary.boundary (PrimeFlagProjection.firstArrow A V x J.val r J.property.1 v G)
      (PrimeFlagProjection.secondArrow A V x J.val r G)) = _ at hh
  dsimp only [PrimeFlagBoundary.boundary]
  rw [← Category.assoc,hh,Category.assoc]
  have hn := (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.naturality
    (TransverseConeBoundary.coneMap (CoordinateFlag.firstArrow S J.val y v G)
      (PrimeFlagProjection.firstArrow A V x J.val r J.property.1 v G)
      (G.map (PrimeFlagPair.oldIso A V x J.val r J.property.1 v).hom)
      (G.map (PrimeFlagPair.fullIso A V x J.val r J.property.1).hom)
      (first_square A V x Allowed G r J v))
  change DerivedCategory.Q.map _ ≫ _ = _ ≫ (oldIso A V x Allowed G r J v).hom⟦(1 : ℤ)⟧' at hn
  rw [hn]
  rfl

variable (herase : ∀ z : J.val, Allowed (J.val.erase z.val))

def targetIso : CoordinateFlag.oldRelative S J.val y v G ≅
    PrimeLayerExcision.localRelative A V x Allowed G r
      (PrimeAdjacentAssembly.edgeIndex V Allowed J.val r J.property.1 herase v) :=
  oldIso A V x Allowed G r J v ≪≫ PrimeFlagBoundary.targetIso A V x Allowed G E r J v herase

theorem block_boundary :
    (PrimeLocalCone.layerIso A V x G Allowed (r+1) J).hom ≫
      PrimeGlobalBoundary.block A V x Allowed G E hall r J
        (PrimeAdjacentAssembly.edgeIndex V Allowed J.val r J.property.1 herase v) =
    CoordinateFlag.boundary S J.val y v G ≫
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (mappingCone (CoordinateFlag.firstArrow S J.val y v G)) ≫
        (targetIso A V x Allowed G E r J v herase).hom⟦(1 : ℤ)⟧' := by
  rw [← fullIso_eq_layerIso,PrimeFlagBoundary.block_boundary]
  simp only [targetIso,Iso.trans_hom,CategoryTheory.Functor.map_comp,Category.assoc]
  rw [reassoc_of% (positive_boundary A V x Allowed G r J v)]

#print axioms first_square
#print axioms second_square
#print axioms oldIso
#print axioms fullIso
#print axioms fullIso_eq_layerIso
#print axioms positive_boundary
#print axioms targetIso
#print axioms block_boundary
end Verification.PrimeCoordinateFlagBoundary
