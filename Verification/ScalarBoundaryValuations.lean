/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarBoundaryOrder
import Verification.ScalarBoundaryPoints

/-!
# Scalar Boundary Valuations

The actual generic-point boundary valuations of the initial
coordinates form the identity matrix. Diagonal entries are DVR orders;
off-diagonal entries vanish because those coordinates are local units.
-/
noncomputable section
namespace Verification.ScalarBoundaryValuations
open Verification.ScalarFrozenGlobal Verification.ScalarDivisorPresentation
open Verification.FrozenAcyclicCover (earlierWeights laterWeights)
open Verification.ExchangeOpenCover
variable (R κ : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (a b : Fin n → Rˣ)
variable (hpos : ∀ r i : Fin n, ¬ r < i → (B (Sum.inl r) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ r i : Fin n, ¬ i < r → (-B (Sum.inl r) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hall : ∀ I : Finset (Fin n), Independent (laterWeights κ n B) I →
  AnticliqueSubcolumns.AS (fun q j => B q (Sum.inl j)) I)

def order (v w : Fin n) : ℕ∞ := by
  letI := ScalarGlobalDomain.global_domain R κ n B a b hpos hneg hsupport hall
  letI := ScalarBoundaryOrder.global_noetherian R κ n B a b
  letI := ScalarDivisorIntegral.divisor_prime R κ n B a b hpos hneg hsupport hall v
  letI := PrincipalBoundaryOrder.discreteValuation (Global R κ n B a b) (divisorIdeal R κ n B a b v)
    (initial R κ n B a b (Sum.inl v))
    (ScalarBoundaryOrder.coordinate_nonzero R κ n B a b hpos hneg hsupport hall v) rfl
  exact IsDiscreteValuationRing.addVal (Localization.AtPrime (divisorIdeal R κ n B a b v))
    (algebraMap (Global R κ n B a b) (Localization.AtPrime (divisorIdeal R κ n B a b v))
      (initial R κ n B a b (Sum.inl w)))

theorem order_self (v : Fin n) : order R κ n B a b hpos hneg hsupport hall v v = 1 :=
  ScalarBoundaryOrder.boundary_order_one R κ n B a b hpos hneg hsupport hall v

theorem order_other (v w : Fin n) (hw : w ≠ v) : order R κ n B a b hpos hneg hsupport hall v w = 0 := by
  letI := ScalarGlobalDomain.global_domain R κ n B a b hpos hneg hsupport hall
  letI := ScalarBoundaryOrder.global_noetherian R κ n B a b
  letI := ScalarDivisorIntegral.divisor_prime R κ n B a b hpos hneg hsupport hall v
  letI := PrincipalBoundaryOrder.discreteValuation (Global R κ n B a b) (divisorIdeal R κ n B a b v)
    (initial R κ n B a b (Sum.inl v))
    (ScalarBoundaryOrder.coordinate_nonzero R κ n B a b hpos hneg hsupport hall v) rfl
  apply IsDiscreteValuationRing.addVal_eq_zero_iff.mpr
  exact IsLocalization.map_units (Localization.AtPrime (divisorIdeal R κ n B a b v))
    (⟨initial R κ n B a b (Sum.inl w),
      ScalarBoundaryPoints.other_not_mem R κ n B a b hpos hneg hsupport hall v w hw⟩ :
      (divisorIdeal R κ n B a b v).primeCompl)

theorem order_matrix (v w : Fin n) : order R κ n B a b hpos hneg hsupport hall v w = if v = w then 1 else 0 := by
  by_cases h : v = w
  · subst w
    rw [if_pos rfl,order_self]
  · rw [if_neg h]
    exact order_other R κ n B a b hpos hneg hsupport hall v w (Ne.symm h)

#print axioms order
#print axioms order_self
#print axioms order_other
#print axioms order_matrix
end Verification.ScalarBoundaryValuations
