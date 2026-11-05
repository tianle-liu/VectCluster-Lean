/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarDivisorPresentation

/-!
# Scalar Freezing Factor

Neighbor partners are eliminated and the removed partner is a free
polynomial variable, for arbitrary scalar exchange coefficients.
-/
noncomputable section
namespace Verification.ScalarFreezingFactor
open MvPolynomial Verification.FrozenAcyclicCover Verification.ActualFreezingDivisor
open Verification.ActualDivisorPresentation (coefficientZeroIdeal initialFamily invertedCoefficient)
open Verification.LocallyClosedPresentation Verification.FreezingIndex
open Verification.ActualFreezingFactor (Base original neighborUnits original_zero neighbor_isUnit)
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (a b : Fin n → Rˣ) (v : Fin n)

def exchange (i : (PUnit.{1} ⊕ Remaining κ n B v) ⊕ Neighbor κ n B v) : Base R κ n B v :=
  baseMap (coefficientZeroIdeal R κ n v) (invertedCoefficient R κ n B v)
    (ScalarFrozenGlobal.exchangeFamily R κ n B a b ((partners κ n B v).symm i))

def residualIdeal : Ideal (MvPolynomial (Remaining κ n B v) (Base R κ n B v)) :=
  FreezingPresentation.remainingIdeal (original R κ n B v) (exchange R κ n B a b v)

abbrev Residual := MvPolynomial (Remaining κ n B v) (Base R κ n B v) ⧸ residualIdeal R κ n B a b v

variable (hpos : ∀ r i : Fin n, ¬ r < i → (B (Sum.inl r) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ r i : Fin n, ¬ i < r → (-B (Sum.inl r) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)

def affineFactorEquiv : ScalarDivisorPresentation.Divisor R κ n B a b v ≃ₐ[R]
    Polynomial (Residual R κ n B a b v) :=
  (ScalarDivisorPresentation.divisorPresentationEquiv R κ n B a b v hpos hneg hsupport).trans
    (((PartnerRelabel.quotientEquiv (partners κ n B v)
      (fun i => baseMap (coefficientZeroIdeal R κ n v) (invertedCoefficient R κ n B v)
        (initialFamily R κ n i))
      (fun i => baseMap (coefficientZeroIdeal R κ n v) (invertedCoefficient R κ n B v)
        (ScalarFrozenGlobal.exchangeFamily R κ n B a b i))).restrictScalars R).trans
      (((FreezingPresentation.preparedEquiv (original R κ n B v) (exchange R κ n B a b v)
        (neighborUnits R κ n B v) (original_zero R κ n B v)
        (fun i => (neighbor_isUnit R κ n B v i).unit_spec.symm)).restrictScalars R).trans
          ((pUnitAlgEquiv (Residual R κ n B a b v)).restrictScalars R)))

#print axioms exchange
#print axioms residualIdeal
#print axioms Residual
#print axioms affineFactorEquiv
end Verification.ScalarFreezingFactor
