/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualIndexedPurity

/-!
# Fixed Global Purity Boundary

Actual global adjacent boundary in both fixed coordinate-purity frames.
The target identification follows from indexed purity naturality and the
constructed adjacent ring isomorphism; no differential law is assumed.
-/
noncomputable section
namespace Verification.FixedGlobalPurityBoundary
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
open Verification.IndependentBasicOpen Verification.IndependentChartIndex
open Verification.IndependentOpenCoordinates Verification.PrimeLayerCover
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable {D : Type*} [Category D] [HasShift D ℤ]
variable (L : DerivedCategory C ⥤ D) [L.CommShift ℤ]
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


def targetComparison :=
  L.map (PrimeLocalCone.layerIso A (Fin n) (fun i => initial R κ n B (Sum.inl i)) G
    (Independent (laterWeights κ n B)) r I).inv ≫
      (P.comparison Wi (Selected n (J.val.erase v.val)) z
        (ActualIndexedPurity.targetFrame R κ n B r J v hpos hneg hsupport hf hs)).hom

include N in
theorem fixed_target_square :
    L.map (PrimeLocalCone.layerIso A (Fin n) (fun i => initial R κ n B (Sum.inl i)) G
      (Independent (laterWeights κ n B)) (r+1) J).hom ≫
    L.map (ActualGlobalBoundary.block R κ n B G E hpos hneg hsupport r J I) ≫
      (L.commShiftIso (1 : ℤ)).hom.app
        (PrimeLayerExcision.localRelative A (Fin n) (fun i => initial R κ n B (Sum.inl i))
          (Independent (laterWeights κ n B)) G r I) ≫
        (targetComparison L R κ n B G P r J v hpos hneg hsupport hf hs)⟦(1 : ℤ)⟧' =
    L.map (CoordinateFlag.boundary W S y v G) ≫
      L.map ((DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
        (mappingCone (CoordinateFlag.firstArrow W S y v G))) ≫
      (L.commShiftIso (1 : ℤ)).hom.app (CoordinateFlag.oldRelative W S y v G) ≫
        ((LocalizedFlagPairs.oldComparison L R W S y v G E P
          (ActualIndexedPurity.sourceFrame R κ n B r J v hpos hneg hsupport hf hs)).hom ≫
            L.map (ActualIndexedPurity.normalTransport R κ n B G r J v))⟦(1 : ℤ)⟧' := by
  have hb := congrArg (fun f => L.map f)
    (ActualGlobalBoundary.adjacent_coordinate_boundary R κ n B G E hpos hneg hsupport r J v)
  simp only [Functor.map_comp,← Category.assoc] at hb
  simp only [targetComparison,Functor.map_comp,Category.assoc]
  rw [← L.commShiftIso_hom_naturality_assoc]
  rw [← Category.assoc,← Category.assoc,hb]
  simp only [Category.assoc]
  erw [reassoc_of% (L.commShiftIso_hom_naturality
    (ActualGlobalBoundary.targetCoordinateIso R κ n B G E r J v).hom (1 : ℤ))]
  rw [← (shiftFunctor D (1 : ℤ)).map_comp]
  rw [ActualIndexedPurity.fixed_target_purity L R κ n B G E P N r J v hpos hneg hsupport hf hs]
  simp only [Functor.map_comp,Category.assoc]

#print axioms targetComparison
#print axioms fixed_target_square
end Verification.FixedGlobalPurityBoundary
