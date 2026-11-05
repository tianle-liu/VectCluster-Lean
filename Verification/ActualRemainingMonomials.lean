/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualFreezingConstraint

/-!
# Actual Remaining Monomials

The other exchange equations in the actual freezing divisor keep
their principal exponents. Their coefficient monomials involve precisely
the invertible neighbour and frozen coordinates.
-/
noncomputable section
namespace Verification.ActualRemainingMonomials
open MvPolynomial Verification.ActualFreezingBase Verification.ActualFreezingFactor
open Verification.ActualDivisorPresentation Verification.ActualFreezingDivisor
open Verification.FreezingOriginalIndex Verification.FreezingIndex
open Verification.LocallyClosedPresentation Verification.FrozenAcyclicCover
open Verification.OriginalTorus
open scoped BigOperators
attribute [local instance] Verification.ActualFreezingConstraint.neighborFintype
attribute [local instance] Verification.ActualFreezingConstraint.remainingFintype
attribute [local instance] Verification.ActualFreezingConstraint.coefficientSelfAction
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (v : Fin n)

def coefficientMonomial (d : (Fin n ⊕ κ) → ℕ) : Torus R (Neighbor κ n B v ⊕ κ) :=
  ∏ a : Neighbor κ n B v ⊕ κ,
    torusCoordinate R (Neighbor κ n B v ⊕ κ) a ^ d (invertedOriginal κ n B v a)

def retainedMonomial (d : (Fin n ⊕ κ) → ℕ) :
    MvPolynomial (Remaining κ n B v) (Torus R (Neighbor κ n B v ⊕ κ)) :=
  ∏ i : Remaining κ n B v, X i ^ d (Sum.inl i.val)

theorem coefficientMonomial_isUnit (d : (Fin n ⊕ κ) → ℕ) :
    IsUnit (coefficientMonomial R κ n B v d) := by
  apply IsUnit.prod_iff.mpr
  intro a _
  exact (torusCoordinate_isUnit R _ a).pow _

theorem map_monomial (d : (Fin n ⊕ κ) → ℕ) (hv : d (Sum.inl v) = 0) :
    baseEquiv R κ n B v
      (baseMap (coefficientZeroIdeal R κ n v) (invertedCoefficient R κ n B v)
        (∏ a, (X a : MvPolynomial (Fin n ⊕ κ) R) ^ d a)) =
      C (coefficientMonomial R κ n B v d) * retainedMonomial R κ n B v d := by
  classical
  simp only [map_prod, map_pow]
  rw [← Fintype.prod_equiv (originals κ n B v).symm
    (fun a => baseEquiv R κ n B v
      (baseMap (coefficientZeroIdeal R κ n v) (invertedCoefficient R κ n B v)
        (X ((originals κ n B v).symm a))) ^ d ((originals κ n B v).symm a))
    (fun a => baseEquiv R κ n B v
      (baseMap (coefficientZeroIdeal R κ n v) (invertedCoefficient R κ n B v)
        (X a)) ^ d a) (fun _ => rfl)]
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Fintype.prod_unique, originals_symm_remaining,
    originals_symm_inverted, baseEquiv_remaining, baseEquiv_inverted,
    coefficientMonomial, retainedMonomial, map_prod, map_pow]
  change _ ^ d (Sum.inl v) * _ = _
  rw [hv, pow_zero, one_mul, mul_comm]

def remainingExchange (i : Remaining κ n B v) :
    MvPolynomial (Remaining κ n B v) (Torus R (Neighbor κ n B v ⊕ κ)) :=
  C (coefficientMonomial R κ n B v (fun a => (B a (Sum.inl i.val)).toNat)) *
      retainedMonomial R κ n B v (fun a => (B a (Sum.inl i.val)).toNat) +
    C (coefficientMonomial R κ n B v (fun a => (-B a (Sum.inl i.val)).toNat)) *
      retainedMonomial R κ n B v (fun a => (-B a (Sum.inl i.val)).toNat)

variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
include hpos hneg hsupport

theorem exchange_image (i : Remaining κ n B v) :
    baseEquiv R κ n B v (exchange R κ n B v (Sum.inl (Sum.inr i))) =
      remainingExchange R κ n B v i := by
  have hz := FreezingSupport.remaining_row κ n B hpos hneg hsupport v i
  change baseEquiv R κ n B v (baseMap _ _
    (Verification.ActualStratum.exchangePolynomial R (Fin n) κ Empty B (Sum.inl i.val))) = _
  rw [Verification.ActualStratum.exchangePolynomial, map_add, map_add]
  rw [map_monomial R κ n B v _ (by rw [hz]; rfl)]
  rw [map_monomial R κ n B v _ (by rw [hz]; rfl)]
  rfl

#print axioms coefficientMonomial
#print axioms retainedMonomial
#print axioms coefficientMonomial_isUnit
#print axioms map_monomial
#print axioms remainingExchange
#print axioms exchange_image
end Verification.ActualRemainingMonomials
