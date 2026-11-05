/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ExplicitStratumTorus
import Verification.GlobalSelectedColumns
import Verification.ActualOpenCoefficients

/-!
# Explicit Stratum Coordinates

Original nonvanishing coordinates, through the actual zero-layer ring
and its explicit affine-torus coordinates.
-/
noncomputable section
set_option maxHeartbeats 80000
set_option synthInstance.maxHeartbeats 20000
namespace Verification.ExplicitStratumCoordinates
open Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.IndependentBasicOpen Verification.GlobalNormalFrame
open Verification.ExchangeOpenCover
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ) (I : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
attribute [local instance] MvPolynomial.algebraMvPolynomial

def original (a : Fin n ⊕ κ) : ZeroLayer R κ n I B :=
  Ideal.Quotient.mk (zeroIdeal R κ n I B)
    (algebraMap (Global R κ n B) (BasicOpen R κ n I B) (initial R κ n B a))

omit [Fintype κ] in
theorem row_originals (a : AnticliqueSubcolumns.Rows (C := κ) I) :
    originals κ n I a.val = Sum.inr (GlobalSelectedColumns.rowEquiv κ n I a) := by
  apply (originals κ n I).symm.injective
  rw [Equiv.symm_apply_apply]
  rcases a with ⟨a,ha⟩
  cases a <;> rfl

theorem chartEquiv_outside (a : AnticliqueSubcolumns.Rows (C := κ) I) :
    chartEquiv R κ n I B
      (algebraMap (Global R κ n B) (BasicOpen R κ n I B) (initial R κ n B a.val)) =
    ActualOpenCoefficients.originalOutside R (Selected n I) (Other n I ⊕ κ) (Other n I)
      Sum.inl (matrix κ n I B) (GlobalSelectedColumns.rowEquiv κ n I a) := by
  change IndependentChartPresentation.openEquiv R κ n I B
    (directEquiv R κ n I B (algebraMap (Global R κ n B) (BasicOpen R κ n I B)
      (algebraMap (PolynomialPresentation R κ n B) (Global R κ n B)
        (FrozenOpenChart.original R (Fin n) κ Empty (noMutable κ) B a.val)))) = _
  rw [← IsScalarTower.algebraMap_apply, AlgEquiv.commutes,
    IndependentOpenCoordinates.presentation_openEquiv_original, row_originals]
  rfl

variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hI : Independent (laterWeights κ n B) I)

theorem affineEquiv_original (a : AnticliqueSubcolumns.Rows (C := κ) I) :
    IndependentStratumCoordinates.affineEquiv R κ n I B hpos hneg hsupport hI
      (original R κ n I B a.val) =
    MvPolynomial.C (Ideal.Quotient.mk (ExchangeTransverseSlice.fiberIdeal
      (ActualOpenChart.characters R (Selected n I) (Other n I ⊕ κ) (Other n I) (matrix κ n I B)))
        (OriginalTorus.torusCoordinate R (Other n I ⊕ κ) (GlobalSelectedColumns.rowEquiv κ n I a))) := by
  rw [original, IndependentStratumCoordinates.affineEquiv_mk, chartEquiv_outside,
    ActualOpenCoefficients.globalOpenEquiv_outside, ExchangeZeroFiber.toAffineRaw_coefficient]

variable (hf : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (hs : FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)))

theorem affineTorusEquiv_original (a : AnticliqueSubcolumns.Rows (C := κ) I) :
    ExplicitStratumTorus.affineTorusEquiv R κ n I B hf hs hpos hneg hsupport hI
      (original R κ n I B a.val) =
    MvPolynomial.C (ExplicitStratumTorus.fiberEquiv R κ n I B hf hs
      (Ideal.Quotient.mk (ExchangeTransverseSlice.fiberIdeal
        (ActualOpenChart.characters R (Selected n I) (Other n I ⊕ κ) (Other n I) (matrix κ n I B)))
        (OriginalTorus.torusCoordinate R (Other n I ⊕ κ) (GlobalSelectedColumns.rowEquiv κ n I a)))) := by
  dsimp only [ExplicitStratumTorus.affineTorusEquiv, AlgEquiv.trans_apply]
  rw [affineEquiv_original]
  exact MvPolynomial.map_C _ _

#print axioms original
#print axioms row_originals
#print axioms chartEquiv_outside
#print axioms affineEquiv_original
#print axioms affineTorusEquiv_original
end Verification.ExplicitStratumCoordinates
