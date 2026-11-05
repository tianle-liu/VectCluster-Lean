/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.IndependentOpenPartners
import Verification.OriginalCanonicalFiberProjection

/-!
# Original Fiber Partner Projection

The actual affine stratum chart sends each original selected partner
to its explicitly invertible negative-monomial multiple of Xi. The genuine
canonical fiber projection therefore kills exactly these partner directions.
-/
noncomputable section
namespace Verification.OriginalFiberPartnerProjection
open MvPolynomial Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.IndependentBasicOpen Verification.IndependentOpenPartners
open Verification.ExchangeOpenCover
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ) (I : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
local notation "Sel" => Selected n I
local notation "Rest" => Other n I
local notation "D" => matrix κ n I B
local notation "χ" => ActualOpenChart.characters R Sel (Rest ⊕ κ) Rest D
local notation "S" => ActualOpenChart.Coefficients R (Rest ⊕ κ)
local notation "New" => ExchangeTransverseSlice.Fiber χ

def partner (i : Sel) : GlobalNormalFrame.ZeroLayer R κ n I B :=
  Ideal.Quotient.mk (GlobalNormalFrame.zeroIdeal R κ n I B) (selectedPartner R κ n I B i)

def negativeUnit (i : Sel) : Newˣ :=
  Units.map (Ideal.Quotient.mk (ExchangeTransverseSlice.fiberIdeal χ)).toMonoidHom
    (ActualOpenChart.negativeUnits R Sel (Rest ⊕ κ) Rest D i)

variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hI : Independent (laterWeights κ n B) I)

theorem affine_partner (i : Sel) :
    IndependentStratumCoordinates.affineEquiv R κ n I B hpos hneg hsupport hI (partner R κ n I B i)=
      C (negativeUnit R κ n I B i : New)*X i := by
  rw [partner,IndependentStratumCoordinates.affineEquiv_mk,chartEquiv_partner,
    ActualOpenPartners.globalOpenEquiv_partner,map_mul,ExchangeZeroFiber.toAffineRaw_coefficient,
    ExchangeZeroFiber.toAffineRaw_y]
  rfl

theorem projection_partner (i : Sel) :
    OriginalCanonicalFiberProjection.projection R κ n I B hpos hneg hsupport hI (partner R κ n I B i)=0 := by
  change PolynomialSectionIso.zeroEvaluation R New Sel
    (IndependentStratumCoordinates.affineEquiv R κ n I B hpos hneg hsupport hI (partner R κ n I B i))=0
  rw [affine_partner,map_mul]
  simp only [PolynomialSectionIso.zeroEvaluation,AlgHom.restrictScalars_apply,aeval_X,mul_zero]

#print axioms partner
#print axioms negativeUnit
#print axioms affine_partner
#print axioms projection_partner
end Verification.OriginalFiberPartnerProjection
