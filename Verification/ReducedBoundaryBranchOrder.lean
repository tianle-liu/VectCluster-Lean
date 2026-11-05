/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrincipalBoundaryOrder
import Verification.RegularPrincipalLocalDomain
import Mathlib.Algebra.Ring.Pi

/-!
# Reduced Boundary Branch Order

A reduced principal divisor may have several domain components. At the
prime over the generic point of any component, its original equation still
generates the local maximal ideal. The component selector is lifted from
the actual quotient; primality of the whole divisor is not assumed.
-/
noncomputable section
namespace Verification.ReducedBoundaryBranchOrder
variable (A : Type*) [CommRing A] (x : A)
variable {J : Type*} (D : J → Type*) [∀ j, CommRing (D j)] [∀ j, IsDomain (D j)]
variable (e : (A ⧸ Ideal.span {x}) ≃+* ∀ j, D j) (j : J)

def projection : A →+* D j :=
  (Pi.evalRingHom D j).comp (e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {x})))

def branch : Ideal A := RingHom.ker (projection A x D e j)

instance branch_prime : (branch A x D e j).IsPrime := by
  letI : (⊥ : Ideal (D j)).IsPrime := Ideal.bot_prime
  exact Ideal.comap_isPrime (projection A x D e j) ⊥

omit [∀ j, IsDomain (D j)] in
theorem mem_branch (a : A) : a ∈ branch A x D e j ↔ e (Ideal.Quotient.mk _ a) j = 0 :=
  Iff.rfl

omit [∀ j, IsDomain (D j)] in
theorem parameter_mem : x ∈ branch A x D e j := by
  rw [mem_branch]
  have h : Ideal.Quotient.mk (Ideal.span {x}) x = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  simp only [h, map_zero, Pi.zero_apply]

/-- One lifted idempotent kills every branch-ideal element modulo the equation. -/
theorem branch_selector : ∃ a : A, a ∉ branch A x D e j ∧
    ∀ z ∈ branch A x D e j, a * z ∈ Ideal.span {x} := by
  classical
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (e.symm (Pi.single j 1))
  have hea : e (Ideal.Quotient.mk (Ideal.span {x}) a) = Pi.single j 1 := by
    rw [ha, e.apply_symm_apply]
  refine ⟨a, ?_, ?_⟩
  · rw [mem_branch, hea]
    simp
  · intro z hz
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply e.injective
    rw [map_zero, map_mul, map_mul, hea]
    funext k
    by_cases hk : k = j
    · subst k
      simpa using (mem_branch A x D e j z).mp hz
    · simp [Pi.single_apply, hk]

/-- Localizing at a selected component removes every other component. -/
theorem maximalIdeal_generated :
    IsLocalRing.maximalIdeal (Localization.AtPrime (branch A x D e j)) =
      Ideal.span {algebraMap A (Localization.AtPrime (branch A x D e j)) x} := by
  let P := branch A x D e j
  let L := Localization.AtPrime P
  let f : A →+* L := algebraMap A L
  let Q : Ideal L := Ideal.span {f x}
  have hmap : Ideal.map f (Ideal.span {x}) = Q := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    obtain ⟨a, ha, haz⟩ := branch_selector A x D e j
    intro z hz
    change f z ∈ Q
    have hunit : IsUnit (f a) :=
      IsLocalization.map_units L (⟨a, ha⟩ : P.primeCompl)
    have hm : f a * f z ∈ Q := by
      rw [← map_mul, ← hmap]
      exact Ideal.mem_map_of_mem f (haz z hz)
    obtain ⟨u, hu⟩ := hunit
    have hc := Q.mul_mem_left (↑(u⁻¹) : L) hm
    simpa only [← hu, ← mul_assoc, Units.inv_mul, one_mul] using hc
  · rw [Ideal.span_le]
    intro z hz
    obtain rfl : z = f x := Set.mem_singleton_iff.mp hz
    exact Ideal.mem_map_of_mem f (parameter_mem A x D e j)

/-- Regularity of the original equation keeps it nonzero at every branch. -/
theorem parameter_nonzero (hx : IsSMulRegular A x) :
    algebraMap A (Localization.AtPrime (branch A x D e j)) x ≠ 0 := by
  intro h
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff (branch A x D e j).primeCompl
    (Localization.AtPrime (branch A x D e j)) x).mp h
  have hz : (s : A) = 0 := hx.eq_zero_of_smul_eq_zero (by
    simpa only [smul_eq_mul, mul_comm] using hs)
  exact s.property (hz ▸ Ideal.zero_mem _)

variable [IsNoetherianRing A]
variable (hx : IsSMulRegular A x)

/-- Local integrality follows from regularity and the proved principal maximal ideal. -/
def localDomain : IsDomain (Localization.AtPrime (branch A x D e j)) := by
  let L := Localization.AtPrime (branch A x D e j)
  letI : IsNoetherianRing L :=
    IsLocalization.isNoetherianRing (branch A x D e j).primeCompl L inferInstance
  exact RegularPrincipalLocalDomain.domain L (algebraMap A L x)
    (maximalIdeal_generated A x D e j)
    (RegularPrincipalLocalDomain.localization_regular A x (branch A x D e j).primeCompl L hx)

/-- A branch has a DVR even when the original divisor has multiple components. -/
def discreteValuation : letI := localDomain A x D e j hx;
    IsDiscreteValuationRing (Localization.AtPrime (branch A x D e j)) := by
  letI := localDomain A x D e j hx
  let L := Localization.AtPrime (branch A x D e j)
  letI : IsNoetherianRing L :=
    IsLocalization.isNoetherianRing (branch A x D e j).primeCompl L inferInstance
  have hpr : (IsLocalRing.maximalIdeal L).IsPrincipal := by
    rw [maximalIdeal_generated A x D e j]
    exact ⟨⟨_, rfl⟩⟩
  letI : IsPrincipalIdealRing L :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain L).out 4 0).mp hpr
  refine { not_a_field' := ?_ }
  intro hm
  have hh : algebraMap A L x ∈ IsLocalRing.maximalIdeal L := by
    rw [maximalIdeal_generated A x D e j]
    exact Ideal.subset_span (Set.mem_singleton _)
  rw [hm] at hh
  exact parameter_nonzero A x D e j hx hh

def order : AddValuation A ℕ∞ := by
  letI := localDomain A x D e j hx
  letI := discreteValuation A x D e j hx
  exact (IsDiscreteValuationRing.addVal (Localization.AtPrime (branch A x D e j))).comap
    (algebraMap A (Localization.AtPrime (branch A x D e j)))

theorem order_parameter : order A x D e j hx x = 1 := by
  letI := localDomain A x D e j hx
  letI := discreteValuation A x D e j hx
  apply IsDiscreteValuationRing.addVal_uniformizer
  exact IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _
    (parameter_nonzero A x D e j hx) (maximalIdeal_generated A x D e j)

theorem order_not_mem (a : A) (ha : a ∉ branch A x D e j) :
    order A x D e j hx a = 0 := by
  letI := localDomain A x D e j hx
  letI := discreteValuation A x D e j hx
  apply IsDiscreteValuationRing.addVal_eq_zero_iff.mpr
  exact IsLocalization.map_units (Localization.AtPrime (branch A x D e j))
    (⟨a, ha⟩ : (branch A x D e j).primeCompl)

#print axioms projection
#print axioms branch
#print axioms branch_prime
#print axioms mem_branch
#print axioms parameter_mem
#print axioms branch_selector
#print axioms maximalIdeal_generated
#print axioms parameter_nonzero
#print axioms localDomain
#print axioms discreteValuation
#print axioms order
#print axioms order_parameter
#print axioms order_not_mem
end Verification.ReducedBoundaryBranchOrder
