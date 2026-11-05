/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.AdjacentCoordinateScheme
import Verification.ActualGlobalBoundary
import Verification.CanonicalFacePair

/-!
# Canonical Adjacent Target

Compatibility of the canonical global face projection with the actual
adjacent coordinate-chart localization. This identifies the fixed target
pair, before imposing any purity or coefficient-theory input.
-/
noncomputable section
namespace Verification.CanonicalAdjacentTarget
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
open Verification.IndependentBasicOpen Verification.IndependentChartIndex
open Verification.IndependentOpenCoordinates Verification.PrimeLayerCover
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (G : Scheme ⥤ CochainComplex C ℤ) (E : OpenConeExcision.StandardExcision G)
variable (r : ℕ) (J : Index (Independent (laterWeights κ n B)) (r+1)) (v : Selected n J.val)
local notation "A" => Global R κ n B
local notation "x" => fun i : Fin n => initial R κ n B (Sum.inl i)
local notation "Allowed" => Independent (laterWeights κ n B)
local notation "S" => Selected n J.val
local notation "W" => BasicOpen R κ n J.val B
local notation "y" => selectedCoordinate R κ n J.val B
local notation "herase" => ActualGlobalBoundary.erase_allowed κ n B r J
local notation "I" => ActualGlobalBoundary.edgeIndex κ n B r J v

set_option maxHeartbeats 400000 in
theorem forward_square :
    (CoordinateLocalizationPair.oldRelativeIso W S y v G E).hom ≫
      (PrimeCoordinateFlagBoundary.oldIso A (Fin n) x Allowed G r J v).hom =
    (AdjacentCoordinatePair.relativeIso n J.val v R κ B G).hom ≫
      (PrimeCanonicalCone.relativeIso A (Fin n) x Allowed G r I).hom ≫
        (PrimeAdjacentAssembly.edgeIso A (Fin n) x Allowed J.val r J.property.1 herase G v).inv ≫
          (PrimeFlagProjection.edgeFlagIso A (Fin n) x J.val r J.property.1 v G E).hom := by
  exact CanonicalFacePair.forward_square A (Fin n) x Allowed G E r J v herase
    (AdjacentCoordinatePair.indexEquiv n J.val v)
    (AdjacentCoordinatePair.equiv n J.val v R κ B).toRingEquiv
    (AdjacentCoordinatePair.equiv_coordinate n J.val v R κ B)
    (AdjacentCoordinateScheme.global_square R κ n J.val B v)

/-- The global face projection uses exactly the adjacent coordinate pair,
with no change of the fixed purity comparison on the target stratum. -/
theorem target_compatibility :
    (CoordinateLocalizationPair.oldRelativeIso W S y v G E).hom ≫
      (ActualGlobalBoundary.targetCoordinateIso R κ n B G E r J v).hom =
    (AdjacentCoordinatePair.relativeIso n J.val v R κ B G).hom := by
  simp only [ActualGlobalBoundary.targetCoordinateIso,ActualGlobalBoundary.targetIso,
    PrimeCoordinateFlagBoundary.targetIso,PrimeFlagBoundary.targetIso,
    Iso.trans_hom,Iso.symm_hom]
  rw [← Category.assoc,← Category.assoc,← Category.assoc,forward_square]
  simp only [Category.assoc,Iso.hom_inv_id_assoc,Iso.inv_hom_id_assoc,
    PrimeCanonicalCone.relativeIso_eq,Iso.hom_inv_id,Category.comp_id]

#print axioms forward_square
#print axioms target_compatibility
end Verification.CanonicalAdjacentTarget
