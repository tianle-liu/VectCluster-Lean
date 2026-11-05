/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualOpenChart

/-!
# Actual Open Coefficients

Exact complementary original-coordinate images in the actual exchange
chart. This supplies the coefficient part of the transverse torus restriction;
no choice of new torus coordinates replaces the original coordinates.
-/
noncomputable section
universe u
namespace Verification.ActualOpenCoefficients
open MvPolynomial Verification.OpenChartPresentation Verification.ActualOpenChart

theorem prepared_coefficient {R T L ι κ : Type u} [CommRing R] [CommRing T] [CommRing L]
    [Algebra R T] [Algebra R L] (E : L ≃ₐ[R] MvPolynomial ι T)
    (x g : (ι ⊕ κ) → L) (u : κ → Lˣ) (a χ : ι → Tˣ)
    (hu : ∀ k, x (Sum.inr k) = (u k : L))
    (hx : ∀ i, E (x (Sum.inl i)) = X i)
    (hg : ∀ i, E (g (Sum.inl i)) = C ((a i : T) * (1 + (χ i : T))))
    (r : L) (t : T) (hr : E r = C t) :
    preparedOpenEquiv E x g u a χ hu hx hg (algebraMap L _ r) =
      algebraMap T (LocalExchangeSmooth.LocalAlgebra χ) t := by
  change residualEquiv E x g a χ hx hg
    ((EliminationWithResidual.exchangeQuotientEquiv x g u hu) (algebraMap L _ r)) = _
  rw [AlgEquiv.commutes]
  change RescaleExchange.quotientEquiv a χ
    (Ideal.Quotient.mk _ (flattenCoefficients E (C r))) = _
  rw [flattenCoefficients_C, hr, flatten_C_C]
  exact (RescaleExchange.quotientEquiv a χ).commutes t

variable (R ι κ τ : Type u) [CommRing R] [Fintype ι] [Fintype κ]
variable (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
variable (hB : ∀ l i : ι, B (Sum.inl l) (Sum.inl i) = 0)

def originalOutside (k : κ) : GlobalOpen R ι κ τ j B :=
  algebraMap (Original R ι κ) (GlobalOpen R ι κ τ j B) (X (Sum.inr k))

theorem globalOpenEquiv_outside (k : κ) :
    globalOpenEquiv R ι κ τ j B hB (originalOutside R ι κ τ j B k) =
      algebraMap (Coefficients R κ) (LocalExchangeSmooth.LocalAlgebra (characters R ι κ τ B))
        (OriginalTorus.torusCoordinate R κ k) := by
  change localizedChartEquiv R ι κ τ j B hB
    ((globalToLocalized R ι κ τ j B) (algebraMap (Original R ι κ) _ (X (Sum.inr k)))) = _
  rw [AlgEquiv.commutes]
  exact prepared_coefficient (PartialOriginalLocalization.openOriginalEquiv R ι κ)
    (localizedInitial R ι κ τ j) (localizedExchange R ι κ τ B)
    (fun t => PartialOriginalLocalization.coordinateUnits R ι κ (j t))
    (negativeUnits R ι κ τ B) (characters R ι κ τ B)
    (localizedInitial_unit R ι κ τ j) (localizedInitial_free R ι κ τ j)
    (localizedExchange_free R ι κ τ B hB) _ _
    (PartialOriginalLocalization.toTarget_coordinate R ι κ (Sum.inr k))

#print axioms prepared_coefficient
#print axioms originalOutside
#print axioms globalOpenEquiv_outside
end Verification.ActualOpenCoefficients
