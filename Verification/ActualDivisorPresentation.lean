/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualFreezingDivisor
import Verification.DivisorLocalization
import Verification.LocallyClosedAlgebra

/-!
# Actual Divisor Presentation

The divisor of the fixed frozen global exchange algebra is identified
with the literal closed/open exchange presentation that inverts only its
neighbors and the frozen coordinates.
-/
noncomputable section
namespace Verification.ActualDivisorPresentation
open MvPolynomial Verification.FrozenAcyclicCover Verification.ActualStratum
open Verification.ActualFreezingDivisor Verification.LocallyClosedPresentation
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (v : Fin n)

def coefficientZeroIdeal : Ideal (OriginalPolynomial R (Fin n) κ) :=
  Ideal.span {X (Sum.inl v)}

abbrev initialFamily := initialPolynomial R (Fin n) κ Empty (noMutable κ)
abbrev exchangeFamily := exchangePolynomial R (Fin n) κ Empty B

def closedIdeal : Ideal (PolynomialPresentation R κ n B) :=
  LocallyClosedPresentation.closedIdeal (coefficientZeroIdeal R κ n v)
    (initialFamily R κ n) (exchangeFamily R κ n B)

def selfAction (A : Type*) [CommRing A] : DistribMulAction A A :=
  (Semiring.toModule : Module A A).toDistribMulAction

local instance closedSelfAction :
    DistribMulAction (PolynomialPresentation R κ n B ⧸ closedIdeal R κ n B v)
      (PolynomialPresentation R κ n B ⧸ closedIdeal R κ n B v) :=
  selfAction (PolynomialPresentation R κ n B ⧸ closedIdeal R κ n B v)

local instance literalClosedSelfAction :
    DistribMulAction
      (ClosedRing (coefficientZeroIdeal R κ n v) (initialFamily R κ n) (exchangeFamily R κ n B))
      (ClosedRing (coefficientZeroIdeal R κ n v) (initialFamily R κ n) (exchangeFamily R κ n B)) :=
  selfAction (ClosedRing (coefficientZeroIdeal R κ n v) (initialFamily R κ n) (exchangeFamily R κ n B))

def invertedOriginal : Neighbor κ n B v ⊕ κ → Fin n ⊕ κ :=
  Sum.elim (fun i => Sum.inl i.1) Sum.inr

def invertedCoefficient : Neighbor κ n B v ⊕ κ → OriginalPolynomial R (Fin n) κ :=
  fun a => X (invertedOriginal κ n B v a)

def largerMonoid : Submonoid (PolynomialPresentation R κ n B) :=
  Submonoid.closure (Set.range (fun a =>
    FrozenOpenChart.original R (Fin n) κ Empty (noMutable κ) B (invertedOriginal κ n B v a)))

theorem closedIdeal_eq : closedIdeal R κ n B v =
    Ideal.span {FrozenOpenChart.original R (Fin n) κ Empty (noMutable κ) B (Sum.inl v)} := by
  simp only [closedIdeal, LocallyClosedPresentation.closedIdeal,
    PolynomialQuotient.coefficientIdeal, coefficientZeroIdeal, Ideal.map_span, Set.image_singleton]
  rfl

theorem localized_closedIdeal :
    (closedIdeal R κ n B v).map (algebraMap (PolynomialPresentation R κ n B) (Global R κ n B)) =
      divisorIdeal R κ n B v := by
  rw [closedIdeal_eq, Ideal.map_span, Set.image_singleton]
  rfl

def toStandard : Divisor R κ n B v ≃+*
    LocalizationQuotient.QuotientLocalized (closedIdeal R κ n B v)
      (FrozenOpenChart.frozenMonoid R (Fin n) κ Empty (noMutable κ) B) :=
  Ideal.quotEquivOfEq (localized_closedIdeal R κ n B v).symm

theorem toStandard_coordinate (a : Fin n ⊕ κ) :
    toStandard R κ n B v (coordinate R κ n B v a) =
      LocalizationQuotient.baseToQuotientLocalized (closedIdeal R κ n B v)
        (FrozenOpenChart.frozenMonoid R (Fin n) κ Empty (noMutable κ) B)
        (FrozenOpenChart.original R (Fin n) κ Empty (noMutable κ) B a) := by
  change Ideal.quotEquivOfEq (localized_closedIdeal R κ n B v).symm
    (Ideal.Quotient.mk _ (initial R κ n B a)) = _
  rw [Ideal.quotEquivOfEq_mk]
  rfl

theorem frozen_le_larger :
    FrozenOpenChart.frozenMonoid R (Fin n) κ Empty (noMutable κ) B ≤ largerMonoid R κ n B v := by
  apply Submonoid.closure_le.mpr
  rintro _ ⟨k, rfl⟩
  apply Submonoid.subset_closure
  exact ⟨Sum.inr k.1, rfl⟩

variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)

include hpos hneg hsupport in
theorem larger_units (a : PolynomialPresentation R κ n B) (ha : a ∈ largerMonoid R κ n B v) :
    IsUnit (LocalizationQuotient.baseToQuotientLocalized (closedIdeal R κ n B v)
      (FrozenOpenChart.frozenMonoid R (Fin n) κ Empty (noMutable κ) B) a) := by
  refine SplitExchangeChart.units_on_closure _ _ (fun q => ?_) ⟨a, ha⟩
  rw [← toStandard_coordinate]
  apply IsUnit.map (toStandard R κ n B v).toRingHom
  cases q with
  | inl i => exact neighbor_unit R κ n B v hpos hneg hsupport i
  | inr k => exact frozen_unit_on_divisor R κ n B v k

theorem map_largerMonoid :
    (largerMonoid R κ n B v).map (Ideal.Quotient.mk (closedIdeal R κ n B v)) =
      openMonoid (coefficientZeroIdeal R κ n v) (initialFamily R κ n) (exchangeFamily R κ n B)
        (invertedCoefficient R κ n B v) := by
  rw [largerMonoid, MonoidHom.map_mclosure, ← Set.range_comp]
  rfl

def localizationCongr {A : Type*} [CommRing A] (M N : Submonoid A) (h : M = N) :
    Localization M ≃ₐ[A] Localization N := by
  subst N
  exact AlgEquiv.refl

def standardLocusEquiv :
    LocalizationQuotient.LocalizedQuotient (closedIdeal R κ n B v) (largerMonoid R κ n B v) ≃+*
      LocallyClosedRing (coefficientZeroIdeal R κ n v) (initialFamily R κ n)
        (exchangeFamily R κ n B) (invertedCoefficient R κ n B v) :=
  (localizationCongr _ _ (map_largerMonoid R κ n B v)).toRingEquiv

def divisorLocusEquiv : Divisor R κ n B v ≃+*
    LocallyClosedRing (coefficientZeroIdeal R κ n v) (initialFamily R κ n)
      (exchangeFamily R κ n B) (invertedCoefficient R κ n B v) :=
  (toStandard R κ n B v).trans
    ((DivisorLocalization.equiv (closedIdeal R κ n B v)
      (FrozenOpenChart.frozenMonoid R (Fin n) κ Empty (noMutable κ) B) (largerMonoid R κ n B v)
      (frozen_le_larger R κ n B v) (larger_units R κ n B v hpos hneg hsupport)).toRingEquiv.trans
        (standardLocusEquiv R κ n B v))

def divisorPresentationEquiv : Divisor R κ n B v ≃+*
    (MvPolynomial (Fin n ⊕ Empty)
      (LocalBase (coefficientZeroIdeal R κ n v) (invertedCoefficient R κ n B v)) ⧸
        StratumPresentation.exchangeIdeal
          (fun i => baseMap (coefficientZeroIdeal R κ n v) (invertedCoefficient R κ n B v)
            (initialFamily R κ n i))
          (fun i => baseMap (coefficientZeroIdeal R κ n v) (invertedCoefficient R κ n B v)
            (exchangeFamily R κ n B i))) :=
  (divisorLocusEquiv R κ n B v hpos hneg hsupport).trans
    (locallyClosedEquiv (coefficientZeroIdeal R κ n v) (initialFamily R κ n)
      (exchangeFamily R κ n B) (invertedCoefficient R κ n B v))

#print axioms coefficientZeroIdeal
#print axioms initialFamily
#print axioms exchangeFamily
#print axioms closedIdeal
#print axioms selfAction
#print axioms closedSelfAction
#print axioms literalClosedSelfAction
#print axioms invertedOriginal
#print axioms invertedCoefficient
#print axioms largerMonoid
#print axioms closedIdeal_eq
#print axioms localized_closedIdeal
#print axioms toStandard
#print axioms toStandard_coordinate
#print axioms frozen_le_larger
#print axioms larger_units
#print axioms map_largerMonoid
#print axioms localizationCongr
#print axioms standardLocusEquiv
#print axioms divisorLocusEquiv
#print axioms divisorPresentationEquiv
end Verification.ActualDivisorPresentation
