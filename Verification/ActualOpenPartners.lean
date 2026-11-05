/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OpenChartPartners
import Verification.ActualOpenChart

/-!
# Actual Open Partners

The literal selected mutated coordinate is sent to its explicit unit
multiple of the normalized y-coordinate under the global chart map.
-/
noncomputable section
universe u
namespace Verification.ActualOpenPartners
open MvPolynomial Verification.ActualOpenChart
open Verification.ActualOpenChart (localizedInitial localizedInitial_unit localizedInitial_free)
open Verification.PartialOriginalLocalization
variable (R ι κ τ : Type u) [CommRing R] [Fintype ι] [Fintype κ]
variable (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
attribute [local instance] MvPolynomial.algebraMvPolynomial

def globalPartner (i : ι) : GlobalOpen R ι κ τ j B :=
  algebraMap _ (GlobalOpen R ι κ τ j B)
    (Ideal.Quotient.mk
      (StratumPresentation.exchangeIdeal (ActualStratum.initialPolynomial R ι κ τ j)
        (ActualStratum.exchangePolynomial R ι κ τ B)) (X (Sum.inl i)))

theorem globalOpenEquiv_partner
    (hB : ∀ l i : ι, B (Sum.inl l) (Sum.inl i) = 0) (i : ι) :
    globalOpenEquiv R ι κ τ j B hB (globalPartner R ι κ τ j B i) =
      algebraMap (Coefficients R κ) (LocalExchangeSmooth.LocalAlgebra (characters R ι κ τ B))
        (negativeUnits R ι κ τ B i : Coefficients R κ) *
      LocalExchangeSmooth.y (characters R ι κ τ B) i := by
  change localizedChartEquiv R ι κ τ j B hB
    ((globalToLocalized R ι κ τ j B) (globalPartner R ι κ τ j B i)) = _
  have hh := LocallyClosedAlgebra.exchangeOpenLocusEquiv_generator (coordinateMonoid R ι κ)
    (ActualStratum.initialPolynomial R ι κ τ j) (ActualStratum.exchangePolynomial R ι κ τ B) (X (Sum.inl i))
  change (globalToLocalized R ι κ τ j B) (globalPartner R ι κ τ j B i) =
    Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap (Original R ι κ) (LocalBase R ι κ)) (X (Sum.inl i))) at hh
  rw [hh,map_X]
  exact OpenChartPartners.preparedOpenEquiv_partner (openOriginalEquiv R ι κ)
    (localizedInitial R ι κ τ j) (localizedExchange R ι κ τ B)
    (fun t => coordinateUnits R ι κ (j t)) (negativeUnits R ι κ τ B) (characters R ι κ τ B)
    (localizedInitial_unit R ι κ τ j) (localizedInitial_free R ι κ τ j)
    (localizedExchange_free R ι κ τ B hB) i

#print axioms globalPartner
#print axioms globalOpenEquiv_partner
end Verification.ActualOpenPartners
