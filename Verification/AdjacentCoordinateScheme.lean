/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.AdjacentCoordinatePair
import Verification.PrimeLocalPair

/-!
# Adjacent Coordinate Scheme

The adjacent chart equivalence commutes with the actual maps to the
original global scheme. This verifies the ambient leg of the canonical
coordinate-pair comparison, not merely the ring isomorphism type.
-/
noncomputable section
namespace Verification.AdjacentCoordinateScheme
open CategoryTheory AlgebraicGeometry
open Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.IndependentBasicOpen Verification.IndependentOpenCoordinates
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (J : Finset (Fin n)) (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (v : Selected n J)
local notation "A" => Global R κ n B
local notation "x" => fun i : Fin n => initial R κ n B (Sum.inl i)
local notation "W" => BasicOpen R κ n J B
local notation "S" => Selected n J
local notation "y" => selectedCoordinate R κ n J B
local notation "Wv" => CoordinateLocalizationPair.OpenRing W S y v
local notation "Wi" => BasicOpen R κ n (J.erase v.val) B

theorem inverse_original (a : A) :
    (AdjacentCoordinatePair.equiv n J v R κ B).symm (algebraMap A Wi a) = algebraMap A Wv a := by
  apply (AdjacentCoordinatePair.equiv n J v R κ B).injective
  rw [AlgEquiv.apply_symm_apply,AdjacentCoordinatePair.equiv_original]

theorem global_square :
    (CoordinatePairEquiv.schemeIso (AdjacentCoordinatePair.equiv n J v R κ B).toRingEquiv).hom ≫
      PrimeLocalPair.inclusion A (Fin n) x (J.erase v.val) =
    CoordinateLocalizationPair.inclusion W S y v ≫ PrimeLocalPair.inclusion A (Fin n) x J := by
  change Spec.map (CommRingCat.ofHom (AdjacentCoordinatePair.equiv n J v R κ B).symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap A Wi)) =
      Spec.map (CommRingCat.ofHom (algebraMap W Wv)) ≫ Spec.map (CommRingCat.ofHom (algebraMap A W))
  rw [← Spec.map_comp,← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change (AdjacentCoordinatePair.equiv n J v R κ B).symm (algebraMap A Wi a) =
    algebraMap W Wv (algebraMap A W a)
  rw [inverse_original,IsScalarTower.algebraMap_apply A W Wv]

#print axioms inverse_original
#print axioms global_square
end Verification.AdjacentCoordinateScheme
