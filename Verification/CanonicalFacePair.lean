/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.CoordinateLocalizationPair
import Verification.CoordinatePairReindex
import Verification.ActualGlobalBoundary
import Verification.StrictConeMapIso
/-!
# Canonical Face Pair

A canonical face comparison for actual localization pairs.
The sole compatibility inputs concern the underlying ring equivalence and
its maps to the original affine scheme; the cone equality is proved.
-/
noncomputable section
namespace Verification.CanonicalFacePair
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.PrimeLayerCover
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (A V : Type) [CommRing A] [Fintype V] [DecidableEq V]
variable (x : V → A) (Allowed : Finset V → Prop)
variable (G : Scheme ⥤ CochainComplex C ℤ) (E : OpenConeExcision.StandardExcision G)
variable (r : ℕ) (J : Index Allowed (r+1)) (v : J.val)
variable (herase : ∀ w : J.val, Allowed (J.val.erase w.val))
variable (ν : CoordinateFlag.Old J.val v ≃ (J.val.erase v.val))
variable (e : CoordinateLocalizationPair.OpenRing (PrimeLocalPair.OpenRing A V x J.val)
  J.val (PrimeLocalPair.coordinate A V x J.val) v ≃+*
  PrimeLocalPair.OpenRing A V x (J.val.erase v.val))
variable (he : ∀ i,e (CoordinateLocalizationPair.coordinate (PrimeLocalPair.OpenRing A V x J.val)
  J.val (PrimeLocalPair.coordinate A V x J.val) v i) =
  PrimeLocalPair.coordinate A V x (J.val.erase v.val) (ν i))
variable (hbase : (CoordinatePairEquiv.schemeIso e).hom ≫
  PrimeLocalPair.inclusion A V x (J.val.erase v.val) =
  CoordinateLocalizationPair.inclusion (PrimeLocalPair.OpenRing A V x J.val) J.val
    (PrimeLocalPair.coordinate A V x J.val) v ≫ PrimeLocalPair.inclusion A V x J.val)
local notation "S" => J.val
local notation "W" => PrimeLocalPair.OpenRing A V x J.val
local notation "y" => PrimeLocalPair.coordinate A V x J.val
local notation "Wv" => CoordinateLocalizationPair.OpenRing W S y v
local notation "Wi" => PrimeLocalPair.OpenRing A V x (J.val.erase v.val)
local notation "z" => PrimeLocalPair.coordinate A V x (J.val.erase v.val)
local notation "q" => CoordinateLocalizationPair.coordinate W S y v
local notation "I" => PrimeAdjacentAssembly.edgeIndex V Allowed J.val r (And.left J.property) herase v

def adjacentIso : CoordinatePurityInput.relative Wv (CoordinateFlag.Old S v) q G ≅
    CoordinatePurityInput.relative Wi (J.val.erase v.val) z G :=
  CoordinatePairEquiv.relativeIso q (z ∘ ν) e he G ≪≫
    (CoordinatePairReindex.relativeIso Wi (J.val.erase v.val) (CoordinateFlag.Old S v) z ν G).symm

include hbase in
set_option maxHeartbeats 800000 in
theorem forward_square :
    (CoordinateLocalizationPair.oldRelativeIso W S y v G E).hom ≫
      (PrimeCoordinateFlagBoundary.oldIso A V x Allowed G r J v).hom =
    (adjacentIso A V x Allowed G r J v ν e he).hom ≫
      (PrimeCanonicalCone.relativeIso A V x Allowed G r I).hom ≫
        (PrimeAdjacentAssembly.edgeIso A V x Allowed J.val r J.property.1 herase G v).inv ≫
          (PrimeFlagProjection.edgeFlagIso A V x J.val r J.property.1 v G E).hom := by
  simp only [CoordinateLocalizationPair.oldRelativeIso,CoordinateLocalizationPair.relativeIso,
    CoordinateFlagExcision.relativeIso,PrimeCoordinateFlagBoundary.oldIso,
    adjacentIso,CoordinatePairEquiv.relativeIso,
    CoordinatePairReindex.relativeIso,PrimeCanonicalCone.relativeIso,
    PrimeAdjacentAssembly.edgeIso,PrimeFlagProjection.edgeFlagIso,PrimeFlagProjection.edgeOldIso,
    Iso.trans_hom,Iso.symm_hom,StrictConeMapIso.inverse_eq]
  simp only [OpenOneExcision.relativeIso,OpenOneExcision.localMap,
    OpenConeExcision.localMap,ConeDerivedComparison.coneIso,asIso_hom,
    TransverseDerivedBoundary.coneMap,TransverseConeBoundary.coneMap,
    ← CategoryTheory.Functor.map_comp,← mappingCone.map_comp]
  congr 1
  simp only [← CategoryTheory.Functor.map_inv, inv_eqToHom, IsIso.inv_id]
  dsimp only [OpenConeExcision.globalArrow,OpenConeExcision.localArrow,CoordinateFlag.firstArrow,
    PrimeFlagProjection.firstArrow,PrimeLayerExcision.openChains,CategoryTheory.Functor.comp_map,
    CoordinateFlag.oldToFull,Scheme.restrictFunctor,Over.forget,Comma.fst,Over.homMk,
    CostructuredArrow.homMk,CostructuredArrow.mk,CategoryTheory.Functor.comp_obj,Over.mk,
    PrimeLocalPair.coordinate,IndependentOpenCoordinates.selectedCoordinate,PrimeLocalPair.OpenRing,
    IndependentBasicOpen.BasicOpen,IndependentBasicOpen.chartValue,ExchangeOpenCover.chartElement,
    PrimeAdjacentAssembly.edgeIndex,
    PrimeAdjacentExcision.edgeChart,PrimeLayerCover.chart,PrimeLocalPair.chartOpen]
  simp only [← mappingCone.map_comp]
  congr 1
  all_goals
    simp only [IsIso.inv_id, Category.comp_id, Category.id_comp, ← CategoryTheory.Functor.map_inv,
      ← CategoryTheory.Functor.map_comp]
    congr 1
  · rw [← cancel_mono (PrimeFlagOpens.old A V x J.val v).ι]
    simp only [Category.assoc,Scheme.homOfLE_ι,PrimeFlagPair.oldIso,Iso.trans_hom,
      Scheme.isoOfEq_hom_ι,Scheme.Hom.isoImage_hom_ι,PrimeCanonicalCone.punctureIso,
      PrimeLocalPair.punctureIso,CoordinateLocalizationPair.punctureIso,
      CoordinatePairReindex.openIso,IsIso.Iso.inv_hom,Scheme.isoOfEq_inv_ι]
    try simp only [Category.assoc,Scheme.homOfLE_ι_assoc,Scheme.isoOfEq_hom_ι_assoc,
      Scheme.Hom.isoImage_hom_ι_assoc,Scheme.isoOfEq_inv_ι_assoc]
    dsimp only [PrimeLocalPair.OpenRing,PrimeLocalPair.coordinate,PrimeLocalPair.chartOpen,
      PrimeLocalPair.previous,IndependentOpenCoordinates.selectedCoordinate,
      IndependentBasicOpen.BasicOpen,IndependentBasicOpen.chartValue,ExchangeOpenCover.chartElement]
    try simp only [Category.assoc,Scheme.homOfLE_ι_assoc,Scheme.homOfLE_ι,
      Scheme.isoOfEq_hom_ι_assoc,Scheme.isoOfEq_hom_ι,
      Scheme.Hom.isoImage_hom_ι_assoc,Scheme.Hom.isoImage_hom_ι,
      Scheme.isoOfEq_inv_ι_assoc,Scheme.isoOfEq_inv_ι]
    change (CoordinateLocalizationPair.punctureIso W S y v).hom ≫
      (CoordinateFlag.oldComplement W S y v ⊓ CoordinateLocalizationPair.chart W S y v).ι ≫
        PrimeLocalPair.inclusion A V x J.val =
      (CoordinatePairEquiv.punctureIso q (z ∘ ν) e he).hom ≫
        (CoordinatePurityInput.puncture Wi (CoordinateFlag.Old S v) (z ∘ ν)).ι ≫
          PrimeLocalPair.inclusion A V x (J.val.erase v.val)
    have hl : (CoordinateLocalizationPair.punctureIso W S y v).hom ≫
        (CoordinateFlag.oldComplement W S y v ⊓ CoordinateLocalizationPair.chart W S y v).ι =
      (CoordinatePurityInput.puncture Wv (CoordinateFlag.Old S v) q).ι ≫
        CoordinateLocalizationPair.inclusion W S y v := by
      simp only [CoordinateLocalizationPair.punctureIso,Iso.trans_hom,Category.assoc,
        Scheme.isoOfEq_hom_ι,Scheme.Hom.isoImage_hom_ι]
    rw [← Category.assoc,hl,Category.assoc,← hbase,← Category.assoc,
      CoordinatePairEquiv.puncture_square,Category.assoc]
  · rw [← cancel_mono (PrimeAdjacentExcision.current A V x J.val r).ι]
    simp only [Category.assoc,Scheme.homOfLE_ι,PrimeFlagPair.fullIso,Iso.trans_hom,
      Scheme.isoOfEq_hom_ι,PrimeLocalPair.punctureIso,Scheme.Hom.isoImage_hom_ι,
      PrimeLocalPair.ambientIso_inclusion]
    dsimp only [PrimeLocalPair.OpenRing,PrimeLocalPair.coordinate,PrimeLocalPair.chartOpen,
      PrimeLocalPair.previous,IndependentOpenCoordinates.selectedCoordinate,
      IndependentBasicOpen.BasicOpen,IndependentBasicOpen.chartValue,ExchangeOpenCover.chartElement]
    try simp only [Category.assoc,Scheme.homOfLE_ι_assoc,Scheme.homOfLE_ι,
      Scheme.isoOfEq_hom_ι_assoc,Scheme.isoOfEq_hom_ι,
      Scheme.Hom.isoImage_hom_ι_assoc,Scheme.Hom.isoImage_hom_ι,
      Scheme.isoOfEq_inv_ι_assoc,Scheme.isoOfEq_inv_ι]
    change (CoordinateLocalizationPair.ambientIso W S y v).hom ≫
      (Spec (CommRingCat.of W)).homOfLE (CoordinateFlagExcision.principal_le W S y v) ≫
        (CoordinateFlag.fullComplement W S y).ι ≫ PrimeLocalPair.inclusion A V x J.val =
      (CoordinatePairEquiv.schemeIso e).hom ≫ (PrimeLocalPair.ambientIso A V x (J.val.erase v.val)).hom ≫
        (PrimeLocalPair.chartOpen A V x (J.val.erase v.val)).ι
    rw [Scheme.homOfLE_ι_assoc,PrimeLocalPair.ambientIso_inclusion]
    rw [← Category.assoc,CoordinateLocalizationPair.ambientIso_inclusion]
    exact hbase.symm

#print axioms adjacentIso
#print axioms forward_square
end Verification.CanonicalFacePair
