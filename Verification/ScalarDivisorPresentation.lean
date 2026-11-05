/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarFrozenGlobal
import Verification.FreezingAlgebra

/-!
# Scalar Divisor Presentation

The whole divisor in a scalar-coefficient acyclic exchange algebra is
its neighbor-localized literal presentation. No extra open subset is used.
-/
noncomputable section
namespace Verification.ScalarDivisorPresentation
open MvPolynomial Verification.ScalarFrozenGlobal Verification.ActualFreezingDivisor
open Verification.LocallyClosedPresentation Verification.FrozenAcyclicCover
open Verification.ActualDivisorPresentation (coefficientZeroIdeal initialFamily invertedCoefficient invertedOriginal selfAction localizationCongr)
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (a b : Fin n → Rˣ) (v : Fin n)

def divisorIdeal : Ideal (ScalarFrozenGlobal.Global R κ n B a b) :=
  Ideal.span {ScalarFrozenGlobal.initial R κ n B a b (Sum.inl v)}
abbrev Divisor := ScalarFrozenGlobal.Global R κ n B a b ⧸ divisorIdeal R κ n B a b v

def coordinate (w : Fin n ⊕ κ) : Divisor R κ n B a b v :=
  Ideal.Quotient.mk _ (ScalarFrozenGlobal.initial R κ n B a b w)

def closedIdeal : Ideal (Presentation R κ n B a b) :=
  LocallyClosedPresentation.closedIdeal (coefficientZeroIdeal R κ n v)
    (initialFamily R κ n) (ScalarFrozenGlobal.exchangeFamily R κ n B a b)

local instance closedSelfAction :
    DistribMulAction (Presentation R κ n B a b ⧸ closedIdeal R κ n B a b v)
      (Presentation R κ n B a b ⧸ closedIdeal R κ n B a b v) :=
  selfAction _

local instance literalClosedSelfAction :
    DistribMulAction
      (ClosedRing (coefficientZeroIdeal R κ n v) (initialFamily R κ n) (ScalarFrozenGlobal.exchangeFamily R κ n B a b))
      (ClosedRing (coefficientZeroIdeal R κ n v) (initialFamily R κ n) (ScalarFrozenGlobal.exchangeFamily R κ n B a b)) :=
  selfAction _

def largerMonoid : Submonoid (Presentation R κ n B a b) :=
  Submonoid.closure (Set.range (fun q => ScalarFrozenGlobal.original R κ n B a b (invertedOriginal κ n B v q)))

theorem closedIdeal_eq : closedIdeal R κ n B a b v =
    Ideal.span {ScalarFrozenGlobal.original R κ n B a b (Sum.inl v)} := by
  simp only [closedIdeal, LocallyClosedPresentation.closedIdeal,
    PolynomialQuotient.coefficientIdeal, coefficientZeroIdeal, Ideal.map_span, Set.image_singleton]
  rfl

theorem localized_closedIdeal :
    (closedIdeal R κ n B a b v).map (algebraMap (Presentation R κ n B a b) (ScalarFrozenGlobal.Global R κ n B a b)) =
      divisorIdeal R κ n B a b v := by
  rw [closedIdeal_eq, Ideal.map_span, Set.image_singleton]
  rfl

def toStandard : Divisor R κ n B a b v ≃ₐ[R]
    LocalizationQuotient.QuotientLocalized (closedIdeal R κ n B a b v)
      (frozenMonoid R κ n B a b) :=
  AlgEquiv.ofRingEquiv (f := Ideal.quotEquivOfEq (localized_closedIdeal R κ n B a b v).symm)
    (fun r => by
      change Ideal.quotEquivOfEq (localized_closedIdeal R κ n B a b v).symm
        (Ideal.Quotient.mk _ (algebraMap R (ScalarFrozenGlobal.Global R κ n B a b) r)) = _
      rw [Ideal.quotEquivOfEq_mk]
      rfl)

theorem toStandard_coordinate (w : Fin n ⊕ κ) :
    toStandard R κ n B a b v (coordinate R κ n B a b v w) =
      LocalizationQuotient.baseToQuotientLocalized (closedIdeal R κ n B a b v)
        (frozenMonoid R κ n B a b) (ScalarFrozenGlobal.original R κ n B a b w) := by
  change Ideal.quotEquivOfEq (localized_closedIdeal R κ n B a b v).symm
    (Ideal.Quotient.mk _ (ScalarFrozenGlobal.initial R κ n B a b w)) = _
  rw [Ideal.quotEquivOfEq_mk]
  rfl

theorem frozen_le_larger : frozenMonoid R κ n B a b ≤ largerMonoid R κ n B a b v := by
  apply Submonoid.closure_le.mpr
  rintro _ ⟨k, rfl⟩
  apply Submonoid.subset_closure
  exact ⟨Sum.inr k, rfl⟩

variable (hpos : ∀ r i : Fin n, ¬ r < i → (B (Sum.inl r) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ r i : Fin n, ¬ i < r → (-B (Sum.inl r) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)

include hpos hneg hsupport in
theorem neighbor_unit (i : Neighbor κ n B v) : IsUnit (coordinate R κ n B a b v (Sum.inl i.1)) :=
  ExchangeRing.neighbor_unit_on_divisor (earlierWeights κ n B) (laterWeights κ n B)
    (fun i => ScalarFrozenGlobal.initial R κ n B a b (Sum.inl i)) (ScalarFrozenGlobal.mutated R κ n B a b)
    (ScalarFrozenGlobal.earlierCoefficient R κ n B a b) (ScalarFrozenGlobal.laterCoefficient R κ n B a b)
    hsupport (ScalarFrozenGlobal.earlierCoefficient_unit R κ n B a b)
    (ScalarFrozenGlobal.ordered_equations R κ n B a b hpos hneg) v i.1 i.2

include hpos hneg hsupport in
theorem larger_units (r : Presentation R κ n B a b) (hr : r ∈ largerMonoid R κ n B a b v) :
    IsUnit (LocalizationQuotient.baseToQuotientLocalized (closedIdeal R κ n B a b v)
      (frozenMonoid R κ n B a b) r) := by
  refine SplitExchangeChart.units_on_closure _ _ (fun q => ?_) ⟨r, hr⟩
  rw [← toStandard_coordinate]
  apply IsUnit.map (toStandard R κ n B a b v).toRingHom
  cases q with
  | inl i => exact neighbor_unit R κ n B a b v hpos hneg hsupport i
  | inr k => exact (ScalarFrozenGlobal.frozen_unit R κ n B a b k).map (Ideal.Quotient.mk _)

theorem map_largerMonoid :
    (largerMonoid R κ n B a b v).map (Ideal.Quotient.mk (closedIdeal R κ n B a b v)) =
      openMonoid (coefficientZeroIdeal R κ n v) (initialFamily R κ n) (ScalarFrozenGlobal.exchangeFamily R κ n B a b)
        (invertedCoefficient R κ n B v) := by
  rw [largerMonoid, MonoidHom.map_mclosure, ← Set.range_comp]
  rfl

def standardLocusEquiv :
    LocalizationQuotient.LocalizedQuotient (closedIdeal R κ n B a b v) (largerMonoid R κ n B a b v) ≃ₐ[R]
      LocallyClosedRing (coefficientZeroIdeal R κ n v) (initialFamily R κ n)
        (ScalarFrozenGlobal.exchangeFamily R κ n B a b) (invertedCoefficient R κ n B v) :=
  (localizationCongr _ _ (map_largerMonoid R κ n B a b v)).restrictScalars R

def divisorLocusEquiv : Divisor R κ n B a b v ≃ₐ[R]
    LocallyClosedRing (coefficientZeroIdeal R κ n v) (initialFamily R κ n)
      (ScalarFrozenGlobal.exchangeFamily R κ n B a b) (invertedCoefficient R κ n B v) :=
  (toStandard R κ n B a b v).trans
    (((DivisorLocalization.equiv (closedIdeal R κ n B a b v)
      (frozenMonoid R κ n B a b) (largerMonoid R κ n B a b v)
      (frozen_le_larger R κ n B a b v) (larger_units R κ n B a b v hpos hneg hsupport)).restrictScalars R).trans
        (standardLocusEquiv R κ n B a b v))

def divisorPresentationEquiv : Divisor R κ n B a b v ≃ₐ[R]
    (MvPolynomial (Fin n ⊕ Empty) (ActualFreezingFactor.Base R κ n B v) ⧸
        StratumPresentation.exchangeIdeal
          (fun i => baseMap (coefficientZeroIdeal R κ n v) (invertedCoefficient R κ n B v)
            (initialFamily R κ n i))
          (fun i => baseMap (coefficientZeroIdeal R κ n v) (invertedCoefficient R κ n B v)
            (ScalarFrozenGlobal.exchangeFamily R κ n B a b i))) :=
  (divisorLocusEquiv R κ n B a b v hpos hneg hsupport).trans
    ((LocallyClosedAlgebra.locallyClosedEquivAlg (coefficientZeroIdeal R κ n v) (initialFamily R κ n)
      (ScalarFrozenGlobal.exchangeFamily R κ n B a b) (invertedCoefficient R κ n B v)).restrictScalars R)

#print axioms divisorIdeal
#print axioms Divisor
#print axioms coordinate
#print axioms closedIdeal
#print axioms closedSelfAction
#print axioms literalClosedSelfAction
#print axioms largerMonoid
#print axioms closedIdeal_eq
#print axioms localized_closedIdeal
#print axioms toStandard
#print axioms toStandard_coordinate
#print axioms frozen_le_larger
#print axioms neighbor_unit
#print axioms larger_units
#print axioms map_largerMonoid
#print axioms standardLocusEquiv
#print axioms divisorLocusEquiv
#print axioms divisorPresentationEquiv
end Verification.ScalarDivisorPresentation
