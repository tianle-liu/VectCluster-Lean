/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FreezingExponentColumns
import Verification.PartnerScaling

/-!
# Normalized Scalar Freezing

Remove the common invertible frozen coefficient from each residual
exchange equation. The resulting coefficient character is exactly the
column of the actual residual AS matrix, and original coordinates are
fixed by the partner rescaling.
-/
noncomputable section
namespace Verification.NormalizedScalarFreezing
open MvPolynomial Verification.ActualScalarFreezing Verification.FreezingExponentColumns
open Verification.ActualResidualColumns Verification.ActualFreezingDivisor Verification.FreezingIndex
open Verification.ActualFreezingCoefficient Verification.FrozenAcyclicCover
open scoped BigOperators
attribute [local instance] Verification.ActualFreezingConstraint.neighborFintype
attribute [local instance] Verification.ActualFreezingConstraint.remainingFintype
attribute [local instance] Verification.ActualScalarFreezing.scalarPolynomialCommRing
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (v : Fin n)
variable (d : Multiplicative (FrozenLattice κ n B v) →* Rˣ)

def normalizedExchange (i : Remaining κ n B v) :
    MvPolynomial (Remaining κ n B v) (Coefficients R κ n B v) :=
  C (scalarMonomial R κ n B v d (neighborColumn κ n B v i.val)) *
      (∏ a : Remaining κ n B v, X a ^ (B (Sum.inl a.val) (Sum.inl i.val)).toNat) +
    ∏ a : Remaining κ n B v, X a ^ (-B (Sum.inl a.val) (Sum.inl i.val)).toNat

def partnerUnit (i : Remaining κ n B v) :
    (MvPolynomial (Remaining κ n B v) (Coefficients R κ n B v))ˣ :=
  Units.map (C : Coefficients R κ n B v →+*
    MvPolynomial (Remaining κ n B v) (Coefficients R κ n B v)).toMonoidHom
      (scalarUnit R κ n B v d (coefficientExponent κ n B v (fun a => (-B a (Sum.inl i.val)).toNat)))

theorem exchange_factor (i : Remaining κ n B v) : scalarExchange R κ n B v d i =
    (partnerUnit R κ n B v d i : MvPolynomial (Remaining κ n B v) (Coefficients R κ n B v)) *
      normalizedExchange R κ n B v d i := by
  change scalarExchange R κ n B v d i =
    C (scalarMonomial R κ n B v d (coefficientExponent κ n B v (fun a => (-B a (Sum.inl i.val)).toNat))) * _
  rw [scalarExchange, exponent_difference, scalarMonomial_add, C_mul, normalizedExchange]
  ring

abbrev NormalizedResidual := MvPolynomial (Remaining κ n B v)
    (MvPolynomial (Remaining κ n B v) (Coefficients R κ n B v)) ⧸
      PartnerScaling.relations (fun i => X i) (normalizedExchange R κ n B v d)

theorem scalarRelations_eq : scalarRelations R κ n B v d =
    PartnerScaling.relations (fun i => X i)
      (fun i => (partnerUnit R κ n B v d i :
        MvPolynomial (Remaining κ n B v) (Coefficients R κ n B v)) * normalizedExchange R κ n B v d i) := by
  unfold scalarRelations PartnerScaling.relations
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  rw [scalarRelation, exchange_factor]
  rfl

def normalizedEquiv : ScalarResidual R κ n B v d ≃ₐ[R] NormalizedResidual R κ n B v d :=
  (Ideal.quotientEquivAlgOfEq R (scalarRelations_eq R κ n B v d)).trans
    (AlgEquiv.ofRingEquiv (f := (PartnerScaling.quotientEquiv (fun i => X i)
      (normalizedExchange R κ n B v d) (partnerUnit R κ n B v d)).toRingEquiv)
        (fun r => PartnerScaling.quotientEquiv_coefficient (fun i => X i)
          (normalizedExchange R κ n B v d) (partnerUnit R κ n B v d)
            (algebraMap R (MvPolynomial (Remaining κ n B v) (Coefficients R κ n B v)) r)))

theorem normalizedEquiv_original (i : Remaining κ n B v) :
    normalizedEquiv R κ n B v d (Ideal.Quotient.mk _ (C (X i))) = Ideal.Quotient.mk _ (C (X i)) := by
  dsimp only [normalizedEquiv, AlgEquiv.trans_apply]
  rw [Ideal.quotientEquivAlgOfEq_mk]
  exact PartnerScaling.quotientEquiv_coefficient (fun i => X i)
    (normalizedExchange R κ n B v d) (partnerUnit R κ n B v d) (X i)

omit d in
theorem quotientLattice_free
    (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
    (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
    (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
    (hAS : AnticliqueSubcolumns.AS (fun a w => B a (Sum.inl w)) ({v} : Finset (Fin n))) :
    Module.Free ℤ (QuotientLattice κ n B v) :=
  PrimitiveLattice.quotient_free (LinearMap.range (columnMap κ n B v))
    (ActualFreezingColumnAS.singleton_AS κ n B v hpos hneg hsupport hAS).2

omit d in
theorem actual_normalized_freezing
    (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
    (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
    (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
    (hAS : AnticliqueSubcolumns.AS (fun a w => B a (Sum.inl w)) ({v} : Finset (Fin n))) :
    ∃ d : Multiplicative (FrozenLattice κ n B v) →* Rˣ,
      d (Multiplicative.ofAdd (distinguishedColumn κ n B v)) = -1 ∧
      Nonempty (Divisor R κ n B v ≃ₐ[R] Polynomial (NormalizedResidual R κ n B v d)) := by
  obtain ⟨d,hd,⟨e⟩⟩ := actual_scalar_freezing R κ n B v hpos hneg hsupport hAS
  exact ⟨d,hd,⟨e.trans (Polynomial.mapAlgEquiv (normalizedEquiv R κ n B v d))⟩⟩

#print axioms normalizedExchange
#print axioms partnerUnit
#print axioms exchange_factor
#print axioms NormalizedResidual
#print axioms scalarRelations_eq
#print axioms normalizedEquiv
#print axioms normalizedEquiv_original
#print axioms quotientLattice_free
#print axioms actual_normalized_freezing
end Verification.NormalizedScalarFreezing
