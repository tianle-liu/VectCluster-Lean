/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarDivisorIntegral
import Verification.PrincipalBoundaryOrder

/-!
# Scalar Boundary Order

Multiplicity one for the actual boundary: the generic-point local
ring of (x_v) is a DVR and its valuation on the original x_v equals one.
-/
noncomputable section
namespace Verification.ScalarBoundaryOrder
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

omit [IsDomain R] in
theorem global_noetherian : IsNoetherianRing (Global R κ n B a b) := by
  letI := ScalarGlobalSmooth.global_finitePresentation R κ n B a b
  exact Algebra.FiniteType.isNoetherianRing R (Global R κ n B a b)

include hpos hneg hsupport hall in
omit [IsNoetherianRing R] in
theorem coordinate_nonzero (v : Fin n) : initial R κ n B a b (Sum.inl v) ≠ 0 := by
  letI := ScalarGlobalDomain.global_domain R κ n B a b hpos hneg hsupport hall
  have hc := ScalarGlobalNonzerodivisors.coordinate_regular R κ n B a b hpos hneg hsupport hall v
  intro hz
  apply (zero_ne_one : (0 : Global R κ n B a b) ≠ 1)
  apply hc
  simp only [hz,zero_smul]

include hpos hneg hsupport hall in
theorem boundary_order_one (v : Fin n) :
    letI := ScalarGlobalDomain.global_domain R κ n B a b hpos hneg hsupport hall;
    letI := global_noetherian R κ n B a b;
    letI := ScalarDivisorIntegral.divisor_prime R κ n B a b hpos hneg hsupport hall v;
    letI := PrincipalBoundaryOrder.discreteValuation (Global R κ n B a b) (divisorIdeal R κ n B a b v)
      (initial R κ n B a b (Sum.inl v))
      (coordinate_nonzero R κ n B a b hpos hneg hsupport hall v) rfl;
    IsDiscreteValuationRing.addVal (Localization.AtPrime (divisorIdeal R κ n B a b v))
      (algebraMap (Global R κ n B a b) (Localization.AtPrime (divisorIdeal R κ n B a b v))
        (initial R κ n B a b (Sum.inl v))) = 1 := by
  letI := ScalarGlobalDomain.global_domain R κ n B a b hpos hneg hsupport hall
  letI := global_noetherian R κ n B a b
  letI := ScalarDivisorIntegral.divisor_prime R κ n B a b hpos hneg hsupport hall v
  exact PrincipalBoundaryOrder.parameter_order_one (Global R κ n B a b) (divisorIdeal R κ n B a b v)
    (initial R κ n B a b (Sum.inl v))
    (coordinate_nonzero R κ n B a b hpos hneg hsupport hall v) rfl

#print axioms global_noetherian
#print axioms coordinate_nonzero
#print axioms boundary_order_one
end Verification.ScalarBoundaryOrder
