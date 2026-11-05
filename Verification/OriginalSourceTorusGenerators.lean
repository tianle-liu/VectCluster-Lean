/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalSourceCoefficientCoordinates

/-!
# Original Source Torus Generators

Literal initial-coordinate images in the actual old Laurent chart:
the new coordinate is the Laurent parameter and every outside coordinate
is its unchanged coefficient unit.
-/
noncomputable section
set_option quotPrecheck false
namespace Verification.OriginalSourceTorusGenerators
open Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.IndependentBasicOpen Verification.IndependentOpenCoordinates
open Verification.OriginalSourceCoefficientCoordinates
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (J : Finset (Fin n)) (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (v : Selected n J)
local notation "A" => Global R κ n B
local notation "W" => BasicOpen R κ n J B
local notation "Sel" => Selected n J
local notation "Rest" => Other n J
local notation "D" => matrix κ n J B
local notation "Wi" => BasicOpen R κ n (J.erase v.val) B
local notation "χ" => ActualOpenChart.characters R Sel (Rest ⊕ κ) Rest D
local notation "OldT" => ActualTorusFace.OldTorus R Sel (Rest ⊕ κ) Rest D v
local notation "OldB" => LocalTransverseOpen.OldFiber χ v

theorem chart_original (a : Fin n ⊕ κ) :
    chartEquiv R κ n J B (algebraMap A W (initial R κ n B a)) =
    algebraMap (IndependentChartPresentation.NewPresentation R κ n J B)
      (ActualOpenChart.GlobalOpen R Sel (Rest ⊕ κ) Rest Sum.inl D)
      (FrozenOpenChart.original R Sel (Rest ⊕ κ) Rest Sum.inl D (originals κ n J a)) := by
  change IndependentChartPresentation.openEquiv R κ n J B
    (directEquiv R κ n J B (algebraMap A W
      (algebraMap (PolynomialPresentation R κ n B) A
        (FrozenOpenChart.original R (Fin n) κ Empty (noMutable κ) B a)))) = _
  rw [← IsScalarTower.algebraMap_apply,AlgEquiv.commutes,presentation_openEquiv_original]

variable (hD : ∀ l i : Selected n J, matrix κ n J B (Sum.inl l) (Sum.inl i) = 0)

theorem parameter : torusMap R κ n J B v hD
    (Ideal.Quotient.mk _ (algebraMap A Wi (initial R κ n B (Sum.inl v.val)))) =
    algebraMap (Polynomial OldB) OldT Polynomial.X := by
  rw [torusMap_original]
  change ActualTorusFace.oldZeroSection R Sel (Rest ⊕ κ) Rest Sum.inl D hD v
    (algebraMap _ _ (Ideal.Quotient.mk _
      (chartEquiv R κ n J B (selectedCoordinate R κ n J B v)))) = _
  rw [chartEquiv_selectedCoordinate]
  change PolynomialSectionIso.zeroEvaluation R OldT (LocalTransverseOpen.Old v)
    (ActualTransverseOpen.affineEquiv R Sel (Rest ⊕ κ) Rest Sum.inl D hD v
      (algebraMap _ _ (ActualTransverseSlice.originalParameter R Sel (Rest ⊕ κ) Rest Sum.inl D v))) = _
  rw [ActualTransverseOpen.affineEquiv_parameter]
  exact MvPolynomial.aeval_C _ _

theorem outside (k : Rest ⊕ κ) : torusMap R κ n J B v hD
    (Ideal.Quotient.mk _ (algebraMap A Wi
      (initial R κ n B ((originals κ n J).symm (Sum.inr k))))) =
    algebraMap (ActualOpenChart.Coefficients R (Rest ⊕ κ)) OldT
      (OriginalTorus.torusCoordinate R (Rest ⊕ κ) k) := by
  rw [torusMap_original,chart_original,Equiv.apply_symm_apply]
  change PolynomialSectionIso.zeroEvaluation R OldT (LocalTransverseOpen.Old v)
    (ActualTransverseOpen.affineEquiv R Sel (Rest ⊕ κ) Rest Sum.inl D hD v
      (algebraMap _ _ (Ideal.Quotient.mk _
        (ActualOpenCoefficients.originalOutside R Sel (Rest ⊕ κ) Rest Sum.inl D k)))) = _
  rw [ActualTransverseOpen.affineEquiv_outside]
  exact MvPolynomial.aeval_C _ _

#print axioms chart_original
#print axioms parameter
#print axioms outside
end Verification.OriginalSourceTorusGenerators
