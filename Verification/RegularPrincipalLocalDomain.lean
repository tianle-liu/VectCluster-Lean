/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Multiplicity
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Regular Principal Local Domain

A noetherian local ring with a regular generator of its maximal ideal
is a domain. This discharges local integrality before invoking the DVR
criterion; it does not import a smoothness-to-integrality assumption.
-/
noncomputable section
namespace Verification.RegularPrincipalLocalDomain
variable (A : Type*) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable (x : A) (hm : IsLocalRing.maximalIdeal A = Ideal.span {x})

include hm in
theorem finite_order (a : A) (ha : a ≠ 0) : FiniteMultiplicity x a := by
  by_contra h
  apply ha
  apply IsHausdorff.haus' (I := IsLocalRing.maximalIdeal A) a
  intro n
  rw [← Ideal.one_eq_top, smul_eq_mul, mul_one, SModEq.zero,
    hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact FiniteMultiplicity.not_iff_forall.mp h n

include hm in
theorem unit_times_power (a : A) (ha : a ≠ 0) :
    ∃ n : ℕ, ∃ u : Aˣ, a = (u : A) * x ^ n := by
  obtain ⟨c, hc, hxc⟩ := (finite_order A x hm a ha).exists_eq_pow_mul_and_not_dvd
  have hu : IsUnit c := by
    apply IsLocalRing.not_mem_maximalIdeal.mp
    rw [hm, Ideal.mem_span_singleton]
    exact hxc
  obtain ⟨u, rfl⟩ := hu
  exact ⟨multiplicity x a, u, hc.trans (mul_comm _ _)⟩

include hm in
theorem regular_of_ne_zero (hx : IsSMulRegular A x) (a : A) (ha : a ≠ 0) :
    IsSMulRegular A a := by
  obtain ⟨n, u, rfl⟩ := unit_times_power A x hm a ha
  exact (u.isUnit.isSMulRegular A).mul (hx.pow n)

include hm in
def domain (hx : IsSMulRegular A x) : IsDomain A := by
  letI : NoZeroDivisors A := ⟨fun {a b} hab => by
    by_cases ha : a = 0
    · exact Or.inl ha
    · exact Or.inr ((regular_of_ne_zero A x hm hx a ha).eq_zero_of_smul_eq_zero hab)⟩
  exact NoZeroDivisors.to_isDomain A

omit [IsLocalRing A] [IsNoetherianRing A] in
theorem localization_regular (M : Submonoid A) (L : Type*) [CommRing L]
    [Algebra A L] [IsLocalization M L] (hx : IsSMulRegular A x) :
    IsSMulRegular L (algebraMap A L x) := by
  apply isSMulRegular_of_smul_eq_zero_imp_eq_zero
  intro z hz
  obtain ⟨⟨a, s⟩, he⟩ := IsLocalization.surj M z
  have hxa : algebraMap A L (x * a) = 0 := by
    rw [map_mul, ← he, ← mul_assoc]
    change (algebraMap A L x • z) * algebraMap A L s = 0
    rw [hz, zero_mul]
  obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff M L (x * a)).mp hxa
  have hta : (t : A) * a = 0 := hx.eq_zero_of_smul_eq_zero (by
    simpa only [smul_eq_mul, mul_left_comm] using ht)
  have ha : algebraMap A L a = 0 :=
    (IsLocalization.map_eq_zero_iff M L a).mpr ⟨t, hta⟩
  exact (IsLocalization.map_units L s).mul_left_eq_zero.mp (he.trans ha)

#print axioms finite_order
#print axioms unit_times_power
#print axioms regular_of_ne_zero
#print axioms domain
#print axioms localization_regular
end Verification.RegularPrincipalLocalDomain
