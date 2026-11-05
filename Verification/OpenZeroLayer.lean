/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualOpenConormal
import Verification.FrozenOpenChart

/-!
# Open Zero Layer

The zero-coordinate quotient used by the conormal frame is the same
actual locally closed stratum used by the Smith and primitive calculations.
This commutes quotient and localization through their proved universal maps.
-/
noncomputable section
universe u
namespace Verification.OpenZeroLayer
open MvPolynomial Verification.ActualStratum Verification.StratumPresentation
open Verification.ActualOpenChart Verification.FrozenOpenChart
variable (R ι κ τ : Type u) [CommRing R] [Fintype ι] [Fintype κ]
variable (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)

abbrev closedIdeal := LocallyClosedPresentation.closedIdeal (zeroCoordinateIdeal R ι κ)
  (initialPolynomial R ι κ τ j) (exchangePolynomial R ι κ τ B)

theorem localized_closedIdeal :
    (closedIdeal R ι κ τ j B).map
      (algebraMap (FrozenOpenChart.Presentation R ι κ τ j B) (GlobalOpen R ι κ τ j B)) =
      ActualOpenConormal.zeroIdeal R ι κ τ j B := by
  simp only [closedIdeal, LocallyClosedPresentation.closedIdeal,
    PolynomialQuotient.coefficientIdeal, zeroCoordinateIdeal, Ideal.map_span,
    ← Set.range_comp, Function.comp_def, ActualOpenConormal.zeroIdeal, ConormalFrame.ideal]
  rfl

theorem closed_complementMonoid :
    (complementMonoid R ι κ τ j B).map (Ideal.Quotient.mk (closedIdeal R ι κ τ j B)) =
      LocallyClosedPresentation.openMonoid (zeroCoordinateIdeal R ι κ)
        (initialPolynomial R ι κ τ j) (exchangePolynomial R ι κ τ B)
        (fun k : κ => X (Sum.inr k)) := by
  simp only [complementMonoid, PolynomialLocalization.coefficientMonoid,
    PartialOriginalLocalization.coordinateMonoid, MonoidHom.map_mclosure,
    ← Set.range_comp, Function.comp_def, LocallyClosedPresentation.openMonoid,
    LocallyClosedPresentation.closedCoefficient]

def stratumEquiv : ActualOpenConormal.ZeroLayer R ι κ τ j B ≃+* GlobalZeroStratum R ι κ τ j B :=
  (Ideal.quotEquivOfEq (localized_closedIdeal R ι κ τ j B).symm).trans
    ((LocalizationQuotient.quotientLocalizationEquiv (closedIdeal R ι κ τ j B)
      (complementMonoid R ι κ τ j B)).trans
      (IsLocalization.ringEquivOfRingEquiv _ _ (RingEquiv.refl _) (by
        simpa using closed_complementMonoid R ι κ τ j B)))

#print axioms closedIdeal
#print axioms localized_closedIdeal
#print axioms closed_complementMonoid
#print axioms stratumEquiv
end Verification.OpenZeroLayer
