/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.RingTheory.Localization.Submodule

/-!
# Principal Boundary Order

A nonzero principal prime in a noetherian domain has a genuine DVR
at its generic point, and the displayed generator has valuation one.
-/
noncomputable section
namespace Verification.PrincipalBoundaryOrder
variable (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
variable (P : Ideal A) [P.IsPrime] (x : A) (hx : x ≠ 0) (hP : P = Ideal.span {x})

include hP in
omit [IsDomain A] [IsNoetherianRing A] in
theorem maximalIdeal_generated : IsLocalRing.maximalIdeal (Localization.AtPrime P) =
    Ideal.span {algebraMap A (Localization.AtPrime P) x} := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  calc
    Ideal.map (algebraMap A (Localization.AtPrime P)) P =
        Ideal.map (algebraMap A (Localization.AtPrime P)) (Ideal.span {x}) :=
      congrArg (Ideal.map (algebraMap A (Localization.AtPrime P))) hP
    _ = _ := by rw [Ideal.map_span,Set.image_singleton]

include hx in
omit [IsNoetherianRing A] in
theorem parameter_nonzero : algebraMap A (Localization.AtPrime P) x ≠ 0 := by
  intro h
  apply hx
  exact (IsLocalization.injective (M := P.primeCompl) (Localization.AtPrime P)
    P.primeCompl_le_nonZeroDivisors) (by simpa only [map_zero] using h)

def discreteValuation : IsDiscreteValuationRing (Localization.AtPrime P) := by
  letI : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl (Localization.AtPrime P) inferInstance
  have hpr : (IsLocalRing.maximalIdeal (Localization.AtPrime P)).IsPrincipal := by
    rw [maximalIdeal_generated A P x hP]
    exact ⟨⟨_,rfl⟩⟩
  letI : IsPrincipalIdealRing (Localization.AtPrime P) :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain
      (Localization.AtPrime P)).out 4 0).mp hpr
  refine { not_a_field' := ?_ }
  intro hm
  have hh : algebraMap A (Localization.AtPrime P) x ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
    rw [maximalIdeal_generated A P x hP]
    exact Ideal.subset_span (Set.mem_singleton _)
  rw [hm] at hh
  exact parameter_nonzero A P x hx hh

theorem parameter_order_one : letI := discreteValuation A P x hx hP;
    IsDiscreteValuationRing.addVal (Localization.AtPrime P)
      (algebraMap A (Localization.AtPrime P) x) = 1 := by
  letI := discreteValuation A P x hx hP
  apply IsDiscreteValuationRing.addVal_uniformizer
  exact IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _
    (parameter_nonzero A P x hx) (maximalIdeal_generated A P x hP)

#print axioms maximalIdeal_generated
#print axioms parameter_nonzero
#print axioms discreteValuation
#print axioms parameter_order_one
end Verification.PrincipalBoundaryOrder
