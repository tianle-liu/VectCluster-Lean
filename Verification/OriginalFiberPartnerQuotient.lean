/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalFiberPartnerProjection
import Verification.ScaledPolynomialProjection

/-!
# Original Fiber Partner Quotient

Killing the actual selected partners gives precisely the canonical torus fiber.
-/
noncomputable section
namespace Verification.OriginalFiberPartnerQuotient
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

open Verification.OriginalFiberPartnerProjection
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hI : Independent (laterWeights κ n B) I)


def partnerIdeal : Ideal (GlobalNormalFrame.ZeroLayer R κ n I B) :=
  Ideal.span (Set.range (partner R κ n I B))

def quotientEquiv :
    (GlobalNormalFrame.ZeroLayer R κ n I B ⧸ partnerIdeal R κ n I B) ≃ₐ[R] New :=
  ScaledPolynomialProjection.quotientEquiv
    (IndependentStratumCoordinates.affineEquiv R κ n I B hpos hneg hsupport hI)
    (partner R κ n I B) (negativeUnit R κ n I B)
    (affine_partner R κ n I B hpos hneg hsupport hI)

theorem quotientEquiv_mk (a : GlobalNormalFrame.ZeroLayer R κ n I B) :
    quotientEquiv R κ n I B hpos hneg hsupport hI
      (Ideal.Quotient.mk (partnerIdeal R κ n I B) a)=
        OriginalCanonicalFiberProjection.projection R κ n I B hpos hneg hsupport hI a := by
  exact ScaledPolynomialProjection.quotientEquiv_mk _ _ _ _ a

theorem projection_surjective : Function.Surjective
    (OriginalCanonicalFiberProjection.projection R κ n I B hpos hneg hsupport hI) :=
  ScaledPolynomialProjection.projection_surjective _

#print axioms partnerIdeal
#print axioms quotientEquiv
#print axioms quotientEquiv_mk
#print axioms projection_surjective
end Verification.OriginalFiberPartnerQuotient
