/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualFreezingBase
import Verification.FreezingSupport

/-!
# Actual Freezing Constraint

Under the actual freezing-base equivalence, the equation at the
removed vertex is a coefficient equation on the neighbour/frozen torus.
Its unit factor and lattice character are computed from the original
matrix column.
-/
noncomputable section
namespace Verification.ActualFreezingConstraint
open MvPolynomial Verification.ActualFreezingBase Verification.ActualFreezingFactor
open Verification.ActualDivisorPresentation Verification.ActualFreezingDivisor
open Verification.FreezingOriginalIndex Verification.FreezingIndex
open Verification.LocallyClosedPresentation Verification.FrozenAcyclicCover
open Verification.OriginalTorus
open scoped BigOperators
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (v : Fin n)

local instance neighborFintype : Fintype (Neighbor κ n B v) := by
  unfold Neighbor
  exact Fintype.ofFinite _
local instance remainingFintype : Fintype (Remaining κ n B v) := Fintype.ofFinite _
local instance coefficientSelfAction : DistribMulAction (SourceQuotient R κ n v)
    (SourceQuotient R κ n v) := selfAction (SourceQuotient R κ n v)

def columnEntry (a : Neighbor κ n B v ⊕ κ) : ℤ :=
  B (invertedOriginal κ n B v a) (Sum.inl v)

def torusExchange : Torus R (Neighbor κ n B v ⊕ κ) :=
  ExchangeCharacters.exchange Finset.univ (columnEntry κ n B v) (fun a => Finsupp.single a 1)

theorem map_monomial (d : (Fin n ⊕ κ) → ℕ)
    (hv : d (Sum.inl v) = 0)
    (hr : ∀ i : Remaining κ n B v, d (Sum.inl i.val) = 0) :
    baseEquiv R κ n B v
      (baseMap (coefficientZeroIdeal R κ n v) (invertedCoefficient R κ n B v)
        (∏ a, (X a : MvPolynomial (Fin n ⊕ κ) R) ^ d a)) =
      C (∏ a : Neighbor κ n B v ⊕ κ,
        torusCoordinate R (Neighbor κ n B v ⊕ κ) a ^ d (invertedOriginal κ n B v a)) := by
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
  simp only [Fintype.prod_unique, originals_symm_free, originals_symm_remaining,
    originals_symm_inverted, hv, hr, pow_zero, Finset.prod_const_one, one_mul,
    baseEquiv_inverted]
  change _ ^ d (Sum.inl v) * _ = _
  rw [hv, pow_zero, one_mul]

variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
include hpos hneg hsupport

theorem exchange_image :
    baseEquiv R κ n B v (exchange R κ n B v (Sum.inl (Sum.inl PUnit.unit))) =
      C (torusExchange R κ n B v) := by
  have hd := FreezingSupport.diagonal κ n B hpos hneg v
  have hr := FreezingSupport.remaining_column κ n B hpos hneg hsupport v
  change baseEquiv R κ n B v (baseMap _ _
    (Verification.ActualStratum.exchangePolynomial R (Fin n) κ Empty B (Sum.inl v))) = _
  rw [Verification.ActualStratum.exchangePolynomial, map_add, map_add]
  rw [map_monomial R κ n B v _ (by rw [hd]; rfl) (fun i => by rw [hr i]; rfl)]
  rw [map_monomial R κ n B v _ (by rw [hd]; rfl) (fun i => by rw [hr i]; rfl)]
  simp only [torusExchange, ExchangeCharacters.exchange, Finset.mem_univ,
    Finset.prod_const, Finset.card_univ, columnEntry, map_add]
  rfl

theorem exchange_factor_image :
    baseEquiv R κ n B v (exchange R κ n B v (Sum.inl (Sum.inl PUnit.unit))) =
      C ((ExchangeCharacters.negativeUnit (R := R) Finset.univ (columnEntry κ n B v)
        (fun a => Finsupp.single a (1 : ℤ)) : Torus R (Neighbor κ n B v ⊕ κ)) *
        (ExchangeCharacters.monomial (ExchangeCharacters.column Finset.univ
          (columnEntry κ n B v) (fun a => Finsupp.single a 1)) - algebraMap R _ (-1))) := by
  rw [exchange_image R κ n B v hpos hneg hsupport]
  exact congrArg C (ExchangeCharacters.exchange_factor _ _ _)

#print axioms columnEntry
#print axioms neighborFintype
#print axioms remainingFintype
#print axioms coefficientSelfAction
#print axioms torusExchange
#print axioms map_monomial
#print axioms exchange_image
#print axioms exchange_factor_image
end Verification.ActualFreezingConstraint
