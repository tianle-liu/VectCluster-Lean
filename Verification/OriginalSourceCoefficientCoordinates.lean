/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualIndexedPurity
import Verification.ActualTorusFace
import Verification.CoordinateFlagLocalization

/-!
# Original Source Coefficient Coordinates

The coefficient ring map underlying the actual old-normal source
transport, before and after its affine zero section. Original exchange
coordinates are transported by their literal quotient/localization maps.
-/
noncomputable section
set_option quotPrecheck false
namespace Verification.OriginalSourceCoefficientCoordinates
open Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.IndependentBasicOpen Verification.IndependentOpenCoordinates
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (J : Finset (Fin n)) (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (v : Selected n J)
local notation "A" => Global R κ n B
local notation "W" => BasicOpen R κ n J B
local notation "Sel" => Selected n J
local notation "Rest" => Other n J
local notation "D" => matrix κ n J B
local notation "x" => selectedCoordinate R κ n J B
local notation "Wv" => CoordinateLocalizationPair.OpenRing W Sel x v
local notation "q" => CoordinateLocalizationPair.coordinate W Sel x v
local notation "Wi" => BasicOpen R κ n (J.erase v.val) B
local notation "z" => selectedCoordinate R κ n (J.erase v.val) B
local notation "e" => AdjacentCoordinatePair.equiv n J v R κ B
local notation "ν" => AdjacentCoordinatePair.indexEquiv n J v
local notation "Q₁" => Wv ⧸ ConormalFrame.ideal q
local notation "O" => ActualTransverseLocalization.OpenSource R Sel (Rest ⊕ κ) Rest Sum.inl D v

theorem inverse_coordinate (i : CoordinateFlag.Old Sel v) : (e).symm (z (ν i)) = q i := by
  apply (e).injective
  rw [AlgEquiv.apply_symm_apply,AdjacentCoordinatePair.equiv_coordinate]

def quotientMap : GlobalNormalFrame.ZeroLayer R κ n (J.erase v.val) B →ₐ[R] Q₁ where
  __ := ReindexedCoordinateMap.closedMap z q ν (e).symm.toRingHom (inverse_coordinate R κ n J B v)
  commutes' r := by
    change Ideal.Quotient.mk _ ((e).symm (algebraMap R Wi r)) = algebraMap R Q₁ r
    rw [AlgEquiv.commutes]
    rfl

def openMap : GlobalNormalFrame.ZeroLayer R κ n (J.erase v.val) B →ₐ[R] O :=
  (ActualCoordinateFlag.openEquiv R κ n J B v).toAlgHom.comp
    ((CoordinateFlagLocalization.closedEquiv R W Sel x v).toAlgHom.comp
      (quotientMap R κ n J B v))

theorem inverse_original (a : A) : (e).symm (algebraMap A Wi a) =
    algebraMap W Wv (algebraMap A W a) := by
  apply (e).injective
  rw [AlgEquiv.apply_symm_apply,← IsScalarTower.algebraMap_apply]
  exact (AdjacentCoordinatePair.equiv_original n J v R κ B a).symm

theorem openMap_original (a : A) :
    openMap R κ n J B v (Ideal.Quotient.mk _ (algebraMap A Wi a)) =
    algebraMap (ActualTransverseSlice.Intermediate R Sel (Rest ⊕ κ) Rest Sum.inl D v) O
      (Ideal.Quotient.mk _ (chartEquiv R κ n J B (algebraMap A W a))) := by
  change ActualCoordinateFlag.openEquiv R κ n J B v
    (CoordinateFlagLocalization.closedEquiv R W Sel x v
      (Ideal.Quotient.mk _ ((e).symm (algebraMap A Wi a)))) = _
  rw [inverse_original,CoordinateFlagLocalization.closedEquiv_generator,
    ActualCoordinateFlag.openEquiv_algebraMap,ActualCoordinateFlag.intermediateEquiv_mk]

variable (hD : ∀ l i : Selected n J, matrix κ n J B (Sum.inl l) (Sum.inl i) = 0)

def torusMap : GlobalNormalFrame.ZeroLayer R κ n (J.erase v.val) B →ₐ[R]
    ActualTorusFace.OldTorus R Sel (Rest ⊕ κ) Rest D v :=
  (ActualTorusFace.oldZeroSection R Sel (Rest ⊕ κ) Rest Sum.inl D hD v).comp
    (openMap R κ n J B v)

theorem torusMap_original (a : A) :
    torusMap R κ n J B v hD (Ideal.Quotient.mk _ (algebraMap A Wi a)) =
    ActualTorusFace.oldZeroSection R Sel (Rest ⊕ κ) Rest Sum.inl D hD v
      (algebraMap (ActualTransverseSlice.Intermediate R Sel (Rest ⊕ κ) Rest Sum.inl D v) O
        (Ideal.Quotient.mk _ (chartEquiv R κ n J B (algebraMap A W a)))) := by
  exact congrArg (ActualTorusFace.oldZeroSection R Sel (Rest ⊕ κ) Rest Sum.inl D hD v)
    (openMap_original R κ n J B v a)

#print axioms inverse_coordinate
#print axioms quotientMap
#print axioms openMap
#print axioms inverse_original
#print axioms openMap_original
#print axioms torusMap
#print axioms torusMap_original
end Verification.OriginalSourceCoefficientCoordinates
