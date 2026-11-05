/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FrozenGlobalSmooth
import Verification.ExchangeRing

/-!
# Actual Freezing Divisor

Every neighbor original is a unit on the actual divisor V(x_v) in
the fixed frozen global exchange algebra. Thus localizing just neighbors
and frozen coordinates leaves the entire divisor unchanged.
-/
noncomputable section
namespace Verification.ActualFreezingDivisor
open Verification.FrozenAcyclicCover
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (v : Fin n)

def divisorIdeal : Ideal (Global R κ n B) := Ideal.span {initial R κ n B (Sum.inl v)}
def Divisor := Global R κ n B ⧸ divisorIdeal R κ n B v

instance divisorCommRing : CommRing (Divisor R κ n B v) :=
  inferInstanceAs (CommRing (Global R κ n B ⧸ divisorIdeal R κ n B v))

def coordinate (i : Fin n ⊕ κ) : Divisor R κ n B v :=
  Ideal.Quotient.mk (divisorIdeal R κ n B v) (initial R κ n B i)

def Neighbor := {i : Fin n // ExchangeRing.Adjacent (laterWeights κ n B) v i}

variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)

include hpos hneg hsupport in
theorem neighbor_unit (i : Neighbor κ n B v) :
    IsUnit (coordinate R κ n B v (Sum.inl i.1)) :=
  ExchangeRing.neighbor_unit_on_divisor (earlierWeights κ n B) (laterWeights κ n B)
    (fun i => initial R κ n B (Sum.inl i)) (mutated R κ n B)
    (earlierCoefficient R κ n B) (laterCoefficient R κ n B) hsupport
    (earlierCoefficient_unit R κ n B) (ordered_equations R κ n B hpos hneg) v i.1 i.2

theorem frozen_unit_on_divisor (k : κ) : IsUnit (coordinate R κ n B v (Sum.inr k)) :=
  (frozen_unit R κ n B k).map (Ideal.Quotient.mk (divisorIdeal R κ n B v))

def invertCoordinate : Neighbor κ n B v ⊕ κ → Divisor R κ n B v :=
  Sum.elim (fun i => coordinate R κ n B v (Sum.inl i.1))
    (fun k => coordinate R κ n B v (Sum.inr k))

def neighborMonoid : Submonoid (Divisor R κ n B v) :=
  Submonoid.closure (Set.range (invertCoordinate R κ n B v))

include hpos hneg hsupport in
theorem neighborMonoid_units : neighborMonoid R κ n B v ≤ IsUnit.submonoid _ := by
  apply Submonoid.closure_le.mpr
  rintro _ ⟨i, rfl⟩
  cases i with
  | inl i => exact neighbor_unit R κ n B v hpos hneg hsupport i
  | inr k => exact frozen_unit_on_divisor R κ n B v k

def localizationEquiv : Divisor R κ n B v ≃ₐ[Divisor R κ n B v]
    Localization (neighborMonoid R κ n B v) :=
  IsLocalization.atUnits (Divisor R κ n B v) (neighborMonoid R κ n B v)
    (neighborMonoid_units R κ n B v hpos hneg hsupport)

#print axioms divisorIdeal
#print axioms Divisor
#print axioms divisorCommRing
#print axioms coordinate
#print axioms Neighbor
#print axioms neighbor_unit
#print axioms frozen_unit_on_divisor
#print axioms invertCoordinate
#print axioms neighborMonoid
#print axioms neighborMonoid_units
#print axioms localizationEquiv
end Verification.ActualFreezingDivisor
