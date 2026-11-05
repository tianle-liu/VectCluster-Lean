/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LaurentBoundaryUnits
import Verification.ScalarBoundaryValuations
import Verification.ScalarInitialUnits

/-!
# Scalar Global Unit Orders

Every actual global unit has order zero at the actual boundary DVRs.
The identity order matrix then kills the mutable exponents in any Laurent
expansion of such a unit, using the proved injective initial localization.
-/
noncomputable section
namespace Verification.ScalarGlobalUnitOrders
open Verification.ScalarFrozenGlobal Verification.ScalarDivisorPresentation
open Verification.ScalarIndependentBasicOpen
open Verification.FrozenAcyclicCover (earlierWeights laterWeights)
open Verification.ExchangeOpenCover
open scoped BigOperators
variable (R κ : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (a b : Fin n → Rˣ)
variable (hpos : ∀ r i : Fin n, ¬ r < i → (B (Sum.inl r) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ r i : Fin n, ¬ i < r → (-B (Sum.inl r) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hall : ∀ I : Finset (Fin n), Independent (laterWeights κ n B) I →
  AnticliqueSubcolumns.AS (fun q j => B q (Sum.inl j)) I)

def valuation (v : Fin n) : AddValuation (Global R κ n B a b) ℕ∞ := by
  letI := ScalarGlobalDomain.global_domain R κ n B a b hpos hneg hsupport hall
  letI := ScalarBoundaryOrder.global_noetherian R κ n B a b
  letI := ScalarDivisorIntegral.divisor_prime R κ n B a b hpos hneg hsupport hall v
  letI := PrincipalBoundaryOrder.discreteValuation (Global R κ n B a b) (divisorIdeal R κ n B a b v)
    (initial R κ n B a b (Sum.inl v))
    (ScalarBoundaryOrder.coordinate_nonzero R κ n B a b hpos hneg hsupport hall v) rfl
  exact (IsDiscreteValuationRing.addVal (Localization.AtPrime (divisorIdeal R κ n B a b v))).comap
    (algebraMap (Global R κ n B a b) (Localization.AtPrime (divisorIdeal R κ n B a b v)))

theorem valuation_coordinate (v w : Fin n) :
    valuation R κ n B a b hpos hneg hsupport hall v (initial R κ n B a b (Sum.inl w)) =
      if v = w then 1 else 0 :=
  ScalarBoundaryValuations.order_matrix R κ n B a b hpos hneg hsupport hall v w

theorem valuation_unit (v : Fin n) (u : (Global R κ n B a b)ˣ) :
    valuation R κ n B a b hpos hneg hsupport hall v (u : Global R κ n B a b) = 0 :=
  LaurentBoundaryUnits.value_unit _ u

include hpos hneg hsupport hall

theorem mutable_exponents_zero (u c : (Global R κ n B a b)ˣ) (z : Fin n → ℤ)
    (h : Units.map (algebraMap (Global R κ n B a b) (BasicOpen R κ n ∅ B a b)).toMonoidHom u =
      Units.map (algebraMap (Global R κ n B a b) (BasicOpen R κ n ∅ B a b)).toMonoidHom c *
        ∏ i, ScalarInitialUnits.localizedUnit R κ n B a b i ^ z i) :
    ∀ i, z i = 0 :=
  LaurentBoundaryUnits.exponents_zero _
    (ScalarGlobalDomain.initial_localization_injective R κ n B a b hpos hneg hsupport hall)
    (fun i => initial R κ n B a b (Sum.inl i))
    (ScalarInitialUnits.localizedUnit R κ n B a b)
    (ScalarInitialUnits.localizedUnit_val R κ n B a b)
    (valuation R κ n B a b hpos hneg hsupport hall)
    (by intro i j; by_cases hij : i = j <;>
      simpa only [hij, if_true, if_false] using
        valuation_coordinate R κ n B a b hpos hneg hsupport hall i j) u c z h

theorem unit_eq_coefficient (u c : (Global R κ n B a b)ˣ) (z : Fin n → ℤ)
    (h : Units.map (algebraMap (Global R κ n B a b) (BasicOpen R κ n ∅ B a b)).toMonoidHom u =
      Units.map (algebraMap (Global R κ n B a b) (BasicOpen R κ n ∅ B a b)).toMonoidHom c *
        ∏ i, ScalarInitialUnits.localizedUnit R κ n B a b i ^ z i) : u = c :=
  LaurentBoundaryUnits.unit_eq_coefficient _
    (ScalarGlobalDomain.initial_localization_injective R κ n B a b hpos hneg hsupport hall)
    (fun i => initial R κ n B a b (Sum.inl i))
    (ScalarInitialUnits.localizedUnit R κ n B a b)
    (ScalarInitialUnits.localizedUnit_val R κ n B a b)
    (valuation R κ n B a b hpos hneg hsupport hall)
    (by intro i j; by_cases hij : i = j <;>
      simpa only [hij, if_true, if_false] using
        valuation_coordinate R κ n B a b hpos hneg hsupport hall i j) u c z h

#print axioms valuation
#print axioms valuation_coordinate
#print axioms valuation_unit
#print axioms mutable_exponents_zero
#print axioms unit_eq_coefficient
end Verification.ScalarGlobalUnitOrders
