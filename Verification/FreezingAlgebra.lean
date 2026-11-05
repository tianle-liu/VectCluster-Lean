/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualFreezingFactor

/-!
# Freezing Algebra

The actual divisor and its affine free-partner decomposition preserve
the ground coefficient algebra, so they define relative affine-scheme
isomorphisms, rather than only absolute ring isomorphisms.
-/
noncomputable section
namespace Verification.FreezingAlgebra
open MvPolynomial Verification.FrozenAcyclicCover Verification.ActualFreezingDivisor
open Verification.ActualDivisorPresentation Verification.LocallyClosedPresentation
open Verification.ActualFreezingFactor Verification.FreezingIndex
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (v : Fin n)
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] ActualDivisorPresentation.closedSelfAction
attribute [local instance] ActualDivisorPresentation.literalClosedSelfAction

instance divisorAlgebra : Algebra R (Divisor R κ n B v) :=
  inferInstanceAs (Algebra R (Global R κ n B ⧸ divisorIdeal R κ n B v))

instance baseAlgebra : Algebra R (Base R κ n B v) :=
  inferInstanceAs (Algebra R (LocalBase (coefficientZeroIdeal R κ n v) (invertedCoefficient R κ n B v)))

instance residualAlgebra : Algebra R (Residual R κ n B v) :=
  inferInstanceAs (Algebra R
    (MvPolynomial (Remaining κ n B v) (Base R κ n B v) ⧸ ActualFreezingFactor.residualIdeal R κ n B v))

def toStandardAlg : Divisor R κ n B v ≃ₐ[R]
    LocalizationQuotient.QuotientLocalized (ActualDivisorPresentation.closedIdeal R κ n B v)
      (FrozenOpenChart.frozenMonoid R (Fin n) κ Empty (noMutable κ) B) :=
  AlgEquiv.ofRingEquiv (f := toStandard R κ n B v) (fun r => by
    change Ideal.quotEquivOfEq (localized_closedIdeal R κ n B v).symm
      (Ideal.Quotient.mk _ (algebraMap R (Global R κ n B) r)) = _
    rw [Ideal.quotEquivOfEq_mk]
    rfl)

def standardLocusAlg :
    LocalizationQuotient.LocalizedQuotient (ActualDivisorPresentation.closedIdeal R κ n B v)
      (largerMonoid R κ n B v) ≃ₐ[R]
    LocallyClosedRing (coefficientZeroIdeal R κ n v) (initialFamily R κ n)
      (exchangeFamily R κ n B) (invertedCoefficient R κ n B v) :=
  (localizationCongr _ _ (map_largerMonoid R κ n B v)).restrictScalars R

variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)

def divisorLocusAlg : Divisor R κ n B v ≃ₐ[R]
    LocallyClosedRing (coefficientZeroIdeal R κ n v) (initialFamily R κ n)
      (exchangeFamily R κ n B) (invertedCoefficient R κ n B v) :=
  (toStandardAlg R κ n B v).trans
    (((DivisorLocalization.equiv (ActualDivisorPresentation.closedIdeal R κ n B v)
      (FrozenOpenChart.frozenMonoid R (Fin n) κ Empty (noMutable κ) B) (largerMonoid R κ n B v)
      (frozen_le_larger R κ n B v) (larger_units R κ n B v hpos hneg hsupport)).restrictScalars R).trans
        (standardLocusAlg R κ n B v))

def divisorPresentationAlg : Divisor R κ n B v ≃ₐ[R]
    (MvPolynomial (Fin n ⊕ Empty) (Base R κ n B v) ⧸
      StratumPresentation.exchangeIdeal
        (fun i => baseMap (coefficientZeroIdeal R κ n v) (invertedCoefficient R κ n B v)
          (initialFamily R κ n i))
        (fun i => baseMap (coefficientZeroIdeal R κ n v) (invertedCoefficient R κ n B v)
          (exchangeFamily R κ n B i))) :=
  (divisorLocusAlg R κ n B v hpos hneg hsupport).trans
    ((LocallyClosedAlgebra.locallyClosedEquivAlg (coefficientZeroIdeal R κ n v)
      (initialFamily R κ n) (exchangeFamily R κ n B) (invertedCoefficient R κ n B v)).restrictScalars R)

def affineFactorAlg : Divisor R κ n B v ≃ₐ[R] Polynomial (Residual R κ n B v) :=
  (divisorPresentationAlg R κ n B v hpos hneg hsupport).trans
    (((PartnerRelabel.quotientEquiv (partners κ n B v)
      (fun i => baseMap (coefficientZeroIdeal R κ n v) (invertedCoefficient R κ n B v)
        (initialFamily R κ n i))
      (fun i => baseMap (coefficientZeroIdeal R κ n v) (invertedCoefficient R κ n B v)
        (exchangeFamily R κ n B i))).restrictScalars R).trans
      (((FreezingPresentation.preparedEquiv (ActualFreezingFactor.original R κ n B v)
        (ActualFreezingFactor.exchange R κ n B v) (neighborUnits R κ n B v) (original_zero R κ n B v)
        (fun i => (neighbor_isUnit R κ n B v i).unit_spec.symm)).restrictScalars R).trans
          ((pUnitAlgEquiv (Residual R κ n B v)).restrictScalars R)))

#print axioms divisorAlgebra
#print axioms baseAlgebra
#print axioms residualAlgebra
#print axioms toStandardAlg
#print axioms standardLocusAlg
#print axioms divisorLocusAlg
#print axioms divisorPresentationAlg
#print axioms affineFactorAlg
end Verification.FreezingAlgebra
