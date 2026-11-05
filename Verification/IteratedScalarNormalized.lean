/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.IteratedScalarFreezing
import Verification.NormalizedScalarFreezing
import Verification.FreezingExponentColumns
import Verification.PartnerScaling

/-!
# Iterated Scalar Normalized

Remove the common invertible frozen coefficient from each residual
exchange equation. The resulting coefficient character is exactly the
column of the actual residual AS matrix, and original coordinates are
fixed by the partner rescaling.
-/
noncomputable section
namespace Verification.IteratedScalarNormalized
open MvPolynomial Verification.IteratedScalarFreezing Verification.FreezingExponentColumns
open Verification.ActualScalarFreezing (FrozenLattice QuotientLattice Coefficients scalarMonomial coefficientExponent)
open Verification.ActualResidualColumns Verification.ActualFreezingDivisor Verification.FreezingIndex
open Verification.ActualFreezingCoefficient Verification.FrozenAcyclicCover
open scoped BigOperators
attribute [local instance] Verification.ActualFreezingConstraint.neighborFintype
attribute [local instance] Verification.ActualFreezingConstraint.remainingFintype
attribute [local instance] Verification.IteratedScalarFreezing.scalarPolynomialCommRing
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (a b : Fin n → Rˣ) (v : Fin n)
variable (d : Multiplicative (FrozenLattice κ n B v) →* Rˣ)

def normalizedExchange (i : Remaining κ n B v) :
    MvPolynomial (Remaining κ n B v) (Coefficients R κ n B v) :=
  C (algebraMap R _ ((a i.val * (b i.val)⁻¹ : Rˣ) : R) *
    scalarMonomial R κ n B v d (neighborColumn κ n B v i.val)) *
      (∏ a : Remaining κ n B v, X a ^ (B (Sum.inl a.val) (Sum.inl i.val)).toNat) +
    ∏ a : Remaining κ n B v, X a ^ (-B (Sum.inl a.val) (Sum.inl i.val)).toNat

def partnerUnit (i : Remaining κ n B v) :
    (MvPolynomial (Remaining κ n B v) (Coefficients R κ n B v))ˣ :=
  Units.map (C : Coefficients R κ n B v →+*
    MvPolynomial (Remaining κ n B v) (Coefficients R κ n B v)).toMonoidHom
      (Units.map (algebraMap R (Coefficients R κ n B v)).toMonoidHom (b i.val) *
        scalarUnit R κ n B v d (coefficientExponent κ n B v (fun a => (-B a (Sum.inl i.val)).toNat)))

theorem exchange_factor (i : Remaining κ n B v) : scalarExchange R κ n B a b v d i =
    (partnerUnit R κ n B b v d i : MvPolynomial (Remaining κ n B v) (Coefficients R κ n B v)) *
      normalizedExchange R κ n B a b v d i := by
  change scalarExchange R κ n B a b v d i =
    C (algebraMap R _ (b i.val : R) *
      scalarMonomial R κ n B v d (coefficientExponent κ n B v (fun r => (-B r (Sum.inl i.val)).toNat))) * _
  rw [scalarExchange, exponent_difference, scalarMonomial_add, normalizedExchange]
  simp only [map_mul, Units.val_mul]
  have hu : C (algebraMap R (Coefficients R κ n B v) (b i.val : R)) *
      C (algebraMap R (Coefficients R κ n B v) ((b i.val)⁻¹ : Rˣ)) =
      (1 : MvPolynomial (Remaining κ n B v) (Coefficients R κ n B v)) := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  linear_combination -(C (algebraMap R (Coefficients R κ n B v) (a i.val : R)) *
    C (scalarMonomial R κ n B v d (coefficientExponent κ n B v (fun r => (-B r (Sum.inl i.val)).toNat))) *
    C (scalarMonomial R κ n B v d (neighborColumn κ n B v i.val)) *
    (∏ r : Remaining κ n B v, X r ^ (B (Sum.inl r.val) (Sum.inl i.val)).toNat)) * hu

abbrev NormalizedResidual := MvPolynomial (Remaining κ n B v)
    (MvPolynomial (Remaining κ n B v) (Coefficients R κ n B v)) ⧸
      PartnerScaling.relations (fun i => X i) (normalizedExchange R κ n B a b v d)

theorem scalarRelations_eq : scalarRelations R κ n B a b v d =
    PartnerScaling.relations (fun i => X i)
      (fun i => (partnerUnit R κ n B b v d i :
        MvPolynomial (Remaining κ n B v) (Coefficients R κ n B v)) * normalizedExchange R κ n B a b v d i) := by
  unfold scalarRelations PartnerScaling.relations
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  rw [scalarRelation, exchange_factor]
  rfl

def normalizedEquiv : ScalarResidual R κ n B a b v d ≃ₐ[R] NormalizedResidual R κ n B a b v d :=
  (Ideal.quotientEquivAlgOfEq R (scalarRelations_eq R κ n B a b v d)).trans
    (AlgEquiv.ofRingEquiv (f := (PartnerScaling.quotientEquiv (fun i => X i)
      (normalizedExchange R κ n B a b v d) (partnerUnit R κ n B b v d)).toRingEquiv)
        (fun r => PartnerScaling.quotientEquiv_coefficient (fun i => X i)
          (normalizedExchange R κ n B a b v d) (partnerUnit R κ n B b v d)
            (algebraMap R (MvPolynomial (Remaining κ n B v) (Coefficients R κ n B v)) r)))

theorem normalizedEquiv_original (i : Remaining κ n B v) :
    normalizedEquiv R κ n B a b v d (Ideal.Quotient.mk _ (C (X i))) = Ideal.Quotient.mk _ (C (X i)) := by
  dsimp only [normalizedEquiv, AlgEquiv.trans_apply]
  rw [Ideal.quotientEquivAlgOfEq_mk]
  exact PartnerScaling.quotientEquiv_coefficient (fun i => X i)
    (normalizedExchange R κ n B a b v d) (partnerUnit R κ n B b v d) (X i)

omit d in
theorem actual_normalized_freezing
    (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
    (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
    (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
    (hAS : AnticliqueSubcolumns.AS (fun a w => B a (Sum.inl w)) ({v} : Finset (Fin n))) :
    ∃ d : Multiplicative (FrozenLattice κ n B v) →* Rˣ,
      d (Multiplicative.ofAdd (distinguishedColumn κ n B v)) = ScalarExchangeCharacters.prescribed (a v) (b v) ∧
      Nonempty (ScalarDivisorPresentation.Divisor R κ n B a b v ≃ₐ[R] Polynomial (NormalizedResidual R κ n B a b v d)) := by
  obtain ⟨d,hd,⟨e⟩⟩ := actual_scalar_freezing R κ n B a b v hpos hneg hsupport hAS
  exact ⟨d,hd,⟨e.trans (Polynomial.mapAlgEquiv (normalizedEquiv R κ n B a b v d))⟩⟩

#print axioms normalizedExchange
#print axioms partnerUnit
#print axioms exchange_factor
#print axioms NormalizedResidual
#print axioms scalarRelations_eq
#print axioms normalizedEquiv
#print axioms normalizedEquiv_original
#print axioms actual_normalized_freezing
end Verification.IteratedScalarNormalized
