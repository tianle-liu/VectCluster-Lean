/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FixedGlobalPurityBoundary

/-!
# Fixed Normalized Boundary

The literal global adjacent block in its fixed target frame equals
the normalized principal flag boundary in its fixed source frame. The
equality is derived from the actual global cone map and ordinary flag
purity; all target transport maps are the constructed ones.
-/
noncomputable section
namespace Verification.FixedNormalizedBoundary
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
open Verification.IndependentBasicOpen Verification.IndependentChartIndex
open Verification.IndependentOpenCoordinates Verification.PrimeLayerCover
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]
variable (L : DerivedCategory C ⥤ D) [L.CommShift ℤ] [L.Additive]
variable (R κ : Type) [CommRing R] [Nontrivial R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (G : Scheme ⥤ CochainComplex C ℤ) (E : OpenConeExcision.StandardExcision G)
variable (P : LocalizedCoordinatePurity.Standard L R G)
variable (N : LocalizedIndexedPurity.Standard L R G P)
variable (r : ℕ) (J : Index (Independent (laterWeights κ n B)) (r+1)) (v : Selected n J.val)
local notation "A" => Global R κ n B
local notation "W" => BasicOpen R κ n J.val B
local notation "S" => Selected n J.val
local notation "y" => selectedCoordinate R κ n J.val B
local notation "Wv" => CoordinateLocalizationPair.OpenRing W S y v
local notation "q" => CoordinateLocalizationPair.coordinate W S y v
local notation "Wi" => BasicOpen R κ n (J.val.erase v.val) B
local notation "I" => ActualGlobalBoundary.edgeIndex κ n B r J v
local notation "z" => selectedCoordinate R κ n (J.val.erase v.val) B
local notation "ν" => AdjacentCoordinatePair.indexEquiv n J.val v
local notation "e" => AdjacentCoordinatePair.equiv n J.val v R κ B

variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hf : ∀ K, Independent (laterWeights κ n B) K →
  Function.Injective (GlobalExchangeSmooth.selectedMap κ n B K))
variable (hs : ∀ K, Independent (laterWeights κ n B) K →
  FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B K)))


variable (K : LocalizedNormalizedFlag.Standard L R G E P)
set_option quotPrecheck false
local notation "oldFrame" => ActualIndexedPurity.sourceFrame R κ n B r J v hpos hneg hsupport hf hs
local notation "o" => (LocalizedActualFlag.oldIso L R κ n J.val B v G E P hpos hneg hsupport (J.property.2) (hf J.val J.property.2) (hs J.val J.property.2))
local notation "a" => ((LocalizedFlagPairs.oldComparison L R W S y v G E P oldFrame).hom ≫ L.map (ActualIndexedPurity.normalTransport R κ n B G r J v))
local notation "U" => ((RelativeProductFunctor.thom R (CoordinateFlag.Old S v) G).obj (RelativeProductAffine.affineOver R (CoordinateFlag.OpenOld W S y v)))

def normalizedBoundary :=
  (P.comparison W S y (IndependentCoordinatePurity.frame R κ n J.val B hpos hneg hsupport
    J.property.2 (hf J.val J.property.2) (hs J.val J.property.2))).hom ≫
  (LocalizedActualFlag.iteratedComparison L R κ n J.val B v G E P K hpos hneg hsupport
    J.property.2 (hf J.val J.property.2) (hs J.val J.property.2)).hom ≫
  L.map (TransverseDerivedBoundary.boundary (RelativeFlagOpenBoundary.openArrow R W S y v G)) ≫
  ((DerivedCategory.Q ⋙ L).commShiftIso (1 : ℤ)).hom.app U ≫
  ((o).inv ≫ a)⟦(1 : ℤ)⟧'

theorem flag_normalized :
    L.map (CoordinateFlag.boundary W S y v G) ≫
      ((DerivedCategory.Q ⋙ L).commShiftIso (1 : ℤ)).hom.app
        (mappingCone (CoordinateFlag.firstArrow W S y v G)) ≫ (a)⟦(1 : ℤ)⟧' =
    normalizedBoundary L R κ n B G E P r J v hpos hneg hsupport hf hs K := by
  have h := LocalizedActualFlag.positive_boundary L R κ n J.val B v G E P K
    hpos hneg hsupport J.property.2 (hf J.val J.property.2) (hs J.val J.property.2)
  have hh := congrArg (fun f => f ≫ ((DerivedCategory.Q ⋙ L).commShiftIso (1 : ℤ)).hom.app U ≫
    ((o).inv ≫ a)⟦(1 : ℤ)⟧') h
  simpa only [normalizedBoundary,LocalizedFlagCoherence.shiftedIso,Iso.trans_hom,Iso.symm_hom,
    Functor.mapIso_hom,Iso.app_hom,Iso.app_inv,Category.assoc,Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp,Iso.hom_inv_id_assoc] using hh.symm

include N in
theorem global_normalized :
    L.map (PrimeLocalCone.layerIso A (Fin n) (fun i => initial R κ n B (Sum.inl i)) G
      (Independent (laterWeights κ n B)) (r+1) J).hom ≫
    L.map (ActualGlobalBoundary.block R κ n B G E hpos hneg hsupport r J I) ≫
      (L.commShiftIso (1 : ℤ)).hom.app
        (PrimeLayerExcision.localRelative A (Fin n) (fun i => initial R κ n B (Sum.inl i))
          (Independent (laterWeights κ n B)) G r I) ≫
        (FixedGlobalPurityBoundary.targetComparison L R κ n B G P r J v hpos hneg hsupport hf hs)⟦(1 : ℤ)⟧' =
    normalizedBoundary L R κ n B G E P r J v hpos hneg hsupport hf hs K := by
  rw [FixedGlobalPurityBoundary.fixed_target_square L R κ n B G E P N r J v hpos hneg hsupport hf hs]
  have h := flag_normalized L R κ n B G E P r J v hpos hneg hsupport hf hs K
  simpa only [Functor.commShiftIso_comp_hom_app,Category.assoc] using h

#print axioms normalizedBoundary
#print axioms flag_normalized
#print axioms global_normalized
end Verification.FixedNormalizedBoundary
