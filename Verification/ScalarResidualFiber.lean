/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarFreezingCoefficient
import Verification.ActualRemainingMonomials
import Verification.FreezingResidualQuotient

/-!
# Scalar Residual Fiber

The actual whole residual divisor presentation, after imposing the
removed vertex's character equation. Original and mutated remaining
coordinates stay distinct: the originals are the inner polynomial
variables, and the partners are the outer variables.
-/
noncomputable section
namespace Verification.ScalarResidualFiber
open MvPolynomial Verification.ActualFreezingFactor Verification.ActualFreezingBase
open Verification.ScalarFreezingCoefficient Verification.ActualFreezingDivisor
open Verification.FreezingIndex Verification.FrozenAcyclicCover
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Verification.ActualFreezingConstraint.neighborFintype
attribute [local instance] Verification.ActualFreezingConstraint.remainingFintype
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (a b : Fin n → Rˣ) (v : Fin n)

abbrev GenericIdeal := FreezingResidualQuotient.coefficientIdeal (ScalarFreezingFactor.exchange R κ n B a b v)

theorem genericIdeal_eq : GenericIdeal R κ n B a b v = constraintIdeal R κ n B a b v := by
  unfold GenericIdeal FreezingResidualQuotient.coefficientIdeal constraintIdeal
  apply congrArg Ideal.span
  ext p
  constructor
  · rintro ⟨u,rfl⟩
    cases u
    exact Set.mem_singleton _
  · rintro rfl
    exact Set.mem_range_self PUnit.unit

def reducedExchange (i : Remaining κ n B v) :
    MvPolynomial (Remaining κ n B v) (TorusFiber R κ n B a b v) :=
  MvPolynomial.map (Ideal.Quotient.mk (torusIdeal R κ n B a b v))
    (ScalarFreezingCoefficient.remainingExchange R κ n B a b v i)

def relation (i : Remaining κ n B v) :
    MvPolynomial (Remaining κ n B v)
      (MvPolynomial (Remaining κ n B v) (TorusFiber R κ n B a b v)) :=
  C (X i) * X i - C (reducedExchange R κ n B a b v i)

def relations : Ideal (MvPolynomial (Remaining κ n B v)
    (MvPolynomial (Remaining κ n B v) (TorusFiber R κ n B a b v))) :=
  Ideal.span (Set.range (relation R κ n B a b v))

abbrev FiberResidual := MvPolynomial (Remaining κ n B v)
    (MvPolynomial (Remaining κ n B v) (TorusFiber R κ n B a b v)) ⧸ relations R κ n B a b v

variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)

def fiberCoeffEquiv : (Base R κ n B v ⧸ GenericIdeal R κ n B a b v) ≃ₐ[R]
    MvPolynomial (Remaining κ n B v) (TorusFiber R κ n B a b v) :=
  (Ideal.quotientEquivAlgOfEq R (genericIdeal_eq R κ n B a b v)).trans
    (constrainedEquiv R κ n B a b v hpos hneg hsupport)

theorem fiberCoeffEquiv_mk (p : Base R κ n B v) :
    fiberCoeffEquiv R κ n B a b v hpos hneg hsupport
      (Ideal.Quotient.mk (GenericIdeal R κ n B a b v) p) =
      MvPolynomial.map (Ideal.Quotient.mk (torusIdeal R κ n B a b v)) (baseEquiv R κ n B v p) := by
  dsimp only [fiberCoeffEquiv, AlgEquiv.trans_apply]
  rw [Ideal.quotientEquivAlgOfEq_mk, constrainedEquiv_mk]

theorem fiberCoeffEquiv_original (i : Remaining κ n B v) :
    fiberCoeffEquiv R κ n B a b v hpos hneg hsupport
      (Ideal.Quotient.mk (GenericIdeal R κ n B a b v) (original R κ n B v (Sum.inl (Sum.inr i)))) = X i := by
  rw [fiberCoeffEquiv_mk, baseEquiv_original, map_X]

theorem fiberCoeffEquiv_exchange (i : Remaining κ n B v) :
    fiberCoeffEquiv R κ n B a b v hpos hneg hsupport
      (Ideal.Quotient.mk (GenericIdeal R κ n B a b v) (ScalarFreezingFactor.exchange R κ n B a b v (Sum.inl (Sum.inr i)))) =
      reducedExchange R κ n B a b v i := by
  rw [fiberCoeffEquiv_mk,
    ScalarFreezingCoefficient.remaining_exchange_image R κ n B a b v hpos hneg hsupport]
  rfl

theorem map_relations :
    (Ideal.span (Set.range (FreezingResidualQuotient.reducedRelation
      (original R κ n B v) (ScalarFreezingFactor.exchange R κ n B a b v)))).map
        (mapAlgEquiv (Remaining κ n B v) (fiberCoeffEquiv R κ n B a b v hpos hneg hsupport)).toRingHom =
      relations R κ n B a b v := by
  rw [Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  change MvPolynomial.map (fiberCoeffEquiv R κ n B a b v hpos hneg hsupport).toRingHom
    (FreezingResidualQuotient.reducedRelation (original R κ n B v) (ScalarFreezingFactor.exchange R κ n B a b v) i) = _
  simp only [FreezingResidualQuotient.reducedRelation, map_sub, map_mul, map_C, map_X]
  change C (fiberCoeffEquiv R κ n B a b v hpos hneg hsupport (Ideal.Quotient.mk _ _)) * X i -
    C (fiberCoeffEquiv R κ n B a b v hpos hneg hsupport (Ideal.Quotient.mk _ _)) = _
  rw [fiberCoeffEquiv_original, fiberCoeffEquiv_exchange]
  rfl

def residualEquiv : ScalarFreezingFactor.Residual R κ n B a b v ≃ₐ[R] FiberResidual R κ n B a b v :=
  ((FreezingResidualQuotient.residualEquiv
    (original R κ n B v) (ScalarFreezingFactor.exchange R κ n B a b v)).restrictScalars R).trans
      (Ideal.quotientEquivAlg _ _
        (mapAlgEquiv (Remaining κ n B v) (fiberCoeffEquiv R κ n B a b v hpos hneg hsupport))
          (map_relations R κ n B a b v hpos hneg hsupport).symm)

def divisorEquiv : ScalarDivisorPresentation.Divisor R κ n B a b v ≃ₐ[R]
    Polynomial (FiberResidual R κ n B a b v) :=
  (ScalarFreezingFactor.affineFactorEquiv R κ n B a b v hpos hneg hsupport).trans
    (Polynomial.mapAlgEquiv (residualEquiv R κ n B a b v hpos hneg hsupport))

#print axioms GenericIdeal
#print axioms genericIdeal_eq
#print axioms reducedExchange
#print axioms relation
#print axioms relations
#print axioms FiberResidual
#print axioms fiberCoeffEquiv
#print axioms fiberCoeffEquiv_mk
#print axioms fiberCoeffEquiv_original
#print axioms fiberCoeffEquiv_exchange
#print axioms map_relations
#print axioms residualEquiv
#print axioms divisorEquiv
end Verification.ScalarResidualFiber
