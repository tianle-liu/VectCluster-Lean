/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarFrozenGlobal
import Verification.ActualDivisorPresentation
import Verification.ActualOpenChart
import Verification.PartnerScaling

/-!
# Scalar Laurent Presentation

The scalar global polynomial/localization presentation is its literal
Laurent-coefficient exchange presentation. This adapter does not assume
acyclicity or a rank condition.
-/
noncomputable section
namespace Verification.ScalarLaurentPresentation
open MvPolynomial Verification.ScalarFrozenGlobal
open Verification.PartialOriginalLocalization Verification.StratumPresentation
open Verification.FrozenAcyclicCover (noMutable)
open Verification.ActualStratum (initialPolynomial OriginalPolynomial)
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (a b : Fin n → Rˣ)
attribute [local instance] MvPolynomial.algebraMvPolynomial

abbrev Original := OriginalPolynomial R (Fin n) κ
abbrev Base := OpenOriginal R (Fin n) κ
abbrev Target := MvPolynomial (Fin n) (OriginalTorus.Torus R κ)

def localizedInitial (i : Fin n ⊕ Empty) : Base R κ n :=
  algebraMap (Original R κ n) (Base R κ n) (initialPolynomial R (Fin n) κ Empty (noMutable κ) i)

def localizedExchange (i : Fin n ⊕ Empty) : Base R κ n :=
  algebraMap (Original R κ n) (Base R κ n) (exchangeFamily R κ n B a b i)

def targetExchange (i : Fin n) : Target R κ n :=
  polynomialMap R (Fin n) κ (scalarExchange R κ n B a b i)

def targetIdeal : Ideal (MvPolynomial (Fin n) (Target R κ n)) :=
  PartnerScaling.relations (fun i => X i) (targetExchange R κ n B a b)

local instance ambientCommRing : CommRing (MvPolynomial (Fin n) (Target R κ n)) := inferInstance

abbrev LaurentPresentation := MvPolynomial (Fin n) (Target R κ n) ⧸ targetIdeal R κ n B a b

theorem monoid_eq : frozenMonoid R κ n B a b =
    (PolynomialLocalization.coefficientMonoid (α := Fin n ⊕ Empty)
      (coordinateMonoid R (Fin n) κ)).map (Ideal.Quotient.mk
        (exchangeIdeal (initialPolynomial R (Fin n) κ Empty (noMutable κ)) (exchangeFamily R κ n B a b))) := by
  rw [PolynomialLocalization.coefficientMonoid, coordinateMonoid,
    MonoidHom.map_mclosure, MonoidHom.map_mclosure, ← Set.range_comp, ← Set.range_comp]
  rfl

abbrev StandardOpen := Localization ((PolynomialLocalization.coefficientMonoid (α := Fin n ⊕ Empty)
    (coordinateMonoid R (Fin n) κ)).map (Ideal.Quotient.mk
      (exchangeIdeal (initialPolynomial R (Fin n) κ Empty (noMutable κ)) (exchangeFamily R κ n B a b))))

def toStandard : Global R κ n B a b ≃ₐ[R] StandardOpen R κ n B a b :=
  (ActualDivisorPresentation.localizationCongr _ _ (monoid_eq R κ n B a b)).restrictScalars R

def globalToLocalized : StandardOpen R κ n B a b ≃ₐ[Original R κ n]
    (MvPolynomial (Fin n ⊕ Empty) (Base R κ n) ⧸
      exchangeIdeal (localizedInitial R κ n) (localizedExchange R κ n B a b)) :=
  AlgEquiv.ofRingEquiv (f := PolynomialLocalization.exchangeOpenLocusEquiv (coordinateMonoid R (Fin n) κ)
    (initialPolynomial R (Fin n) κ Empty (noMutable κ)) (exchangeFamily R κ n B a b)) (fun p => by
      simpa only [map_C] using LocallyClosedAlgebra.exchangeOpenLocusEquiv_generator (coordinateMonoid R (Fin n) κ)
        (initialPolynomial R (Fin n) κ Empty (noMutable κ)) (exchangeFamily R κ n B a b) (C p))

omit [Fintype κ] in
theorem target_initial (i : Fin n) :
    openOriginalEquiv R (Fin n) κ (localizedInitial R κ n (Sum.inl i)) = X i :=
  toTarget_coordinate R (Fin n) κ (Sum.inl i)

theorem target_exchange (i : Fin n) :
    openOriginalEquiv R (Fin n) κ (localizedExchange R κ n B a b (Sum.inl i)) =
      targetExchange R κ n B a b i :=
  ActualOpenChart.originalEquiv_generator R (Fin n) κ (scalarExchange R κ n B a b i)

theorem map_residualIdeal :
    (EliminationWithResidual.residualIdeal (localizedInitial R κ n) (localizedExchange R κ n B a b)).map
      (mapAlgEquiv (Fin n) (openOriginalEquiv R (Fin n) κ)).toRingHom = targetIdeal R κ n B a b := by
  rw [EliminationWithResidual.residualIdeal, targetIdeal, PartnerScaling.relations,
    Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  change MvPolynomial.map (openOriginalEquiv R (Fin n) κ).toRingHom
    (EliminationWithResidual.residualRelation (localizedInitial R κ n) (localizedExchange R κ n B a b) i) = _
  simp only [EliminationWithResidual.residualRelation, map_sub, map_mul, map_C, map_X]
  change C (openOriginalEquiv R (Fin n) κ (localizedInitial R κ n (Sum.inl i))) * X i -
    C (openOriginalEquiv R (Fin n) κ (localizedExchange R κ n B a b (Sum.inl i))) = _
  rw [target_initial, target_exchange]
  rfl

def globalEquiv : Global R κ n B a b ≃ₐ[R] LaurentPresentation R κ n B a b :=
  (toStandard R κ n B a b).trans
    (((globalToLocalized R κ n B a b).restrictScalars R).trans
      (((EliminationWithResidual.exchangeQuotientEquiv (localizedInitial R κ n)
        (localizedExchange R κ n B a b) (fun e : Empty => e.elim) (fun e => e.elim)).restrictScalars R).trans
          (Ideal.quotientEquivAlg _ _ (mapAlgEquiv (Fin n) (openOriginalEquiv R (Fin n) κ))
            (map_residualIdeal R κ n B a b).symm)))

#print axioms Original
#print axioms Base
#print axioms Target
#print axioms localizedInitial
#print axioms localizedExchange
#print axioms targetExchange
#print axioms targetIdeal
#print axioms ambientCommRing
#print axioms LaurentPresentation
#print axioms monoid_eq
#print axioms StandardOpen
#print axioms toStandard
#print axioms globalToLocalized
#print axioms target_initial
#print axioms target_exchange
#print axioms map_residualIdeal
#print axioms globalEquiv
end Verification.ScalarLaurentPresentation
