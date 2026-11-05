/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Data.ENat.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Laurent Boundary Units

Clearing the positive and negative exponents in a Laurent unit identity
reduces exponent detection to ordinary nonnegative DVR orders in the original
ring. No extension of a valuation to a fraction field is assumed.
-/
noncomputable section
namespace Verification.LaurentBoundaryUnits
open scoped BigOperators
variable {A T I : Type*} [CommRing A] [CommRing T] [Fintype I]
attribute [local instance] Classical.propDecidable

theorem value_unit (v : AddValuation A ℕ∞) (u : Aˣ) : v (u : A) = 0 := by
  have h : v (u : A) + v ((u⁻¹ : Aˣ) : A) = 0 := by
    rw [← v.map_mul, Units.mul_inv, v.map_one]
  exact le_antisymm (by rw [← h]; exact le_self_add) (zero_le _)

omit [Fintype I] in
theorem value_prod (v : AddValuation A ℕ∞) (s : Finset I) (f : I → A) :
    v (∏ i ∈ s, f i) = ∑ i ∈ s, v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [v.map_one]
  | @insert i s hi ih => simp only [Finset.prod_insert hi, Finset.sum_insert hi, v.map_mul, ih]

theorem value_monomial (v : AddValuation A ℕ∞) (x : I → A) (i : I)
    (hx : ∀ j, v (x j) = if i = j then 1 else 0) (m : I → ℕ) :
    v (∏ j, x j ^ m j) = (m i : ℕ∞) := by
  classical
  rw [value_prod]
  simp only [v.map_pow, hx, smul_ite, nsmul_one, nsmul_zero]
  simp

theorem zpow_clear (X : Tˣ) (z : ℤ) :
    X ^ z * X ^ (-z).toNat = X ^ z.toNat := by
  rw [← zpow_natCast, ← zpow_add, ← zpow_natCast]
  congr 1
  omega

/-- Equality in the localized unit group gives a cleared equality in A. -/
theorem cleared_identity (f : A →+* T) (hf : Function.Injective f)
    (x : I → A) (X : I → Tˣ) (hX : ∀ i, (X i : T) = f (x i))
    (u c : Aˣ) (z : I → ℤ)
    (h : Units.map f.toMonoidHom u = Units.map f.toMonoidHom c * ∏ i, X i ^ z i) :
    (u : A) * ∏ i, x i ^ (-z i).toNat = (c : A) * ∏ i, x i ^ (z i).toNat := by
  have he : Units.map f.toMonoidHom u * ∏ i, X i ^ (-z i).toNat =
      Units.map f.toMonoidHom c * ∏ i, X i ^ (z i).toNat := by
    rw [h, mul_assoc, ← Finset.prod_mul_distrib]
    simp only [zpow_clear]
  apply hf
  simpa [map_prod, hX] using congrArg Units.val he

/-- A unit has zero exponent along each multiplicity-one coordinate boundary. -/
theorem exponents_zero (f : A →+* T) (hf : Function.Injective f)
    (x : I → A) (X : I → Tˣ) (hX : ∀ i, (X i : T) = f (x i))
    (v : I → AddValuation A ℕ∞)
    (hv : ∀ i j, v i (x j) = if i = j then 1 else 0)
    (u c : Aˣ) (z : I → ℤ)
    (h : Units.map f.toMonoidHom u = Units.map f.toMonoidHom c * ∏ i, X i ^ z i) :
    ∀ i, z i = 0 := by
  intro i
  have he := congrArg (v i) (cleared_identity f hf x X hX u c z h)
  rw [(v i).map_mul, (v i).map_mul, value_unit, value_unit,
    zero_add, zero_add, value_monomial (v i) x i (hv i),
    value_monomial (v i) x i (hv i)] at he
  have hn := ENat.coe_inj.mp he
  omega

theorem unit_eq_coefficient (f : A →+* T) (hf : Function.Injective f)
    (x : I → A) (X : I → Tˣ) (hX : ∀ i, (X i : T) = f (x i))
    (v : I → AddValuation A ℕ∞)
    (hv : ∀ i j, v i (x j) = if i = j then 1 else 0)
    (u c : Aˣ) (z : I → ℤ)
    (h : Units.map f.toMonoidHom u = Units.map f.toMonoidHom c * ∏ i, X i ^ z i) : u = c := by
  have hz := exponents_zero f hf x X hX v hv u c z h
  simp only [hz, zpow_zero, Finset.prod_const_one, mul_one] at h
  apply Units.ext
  exact hf (congrArg Units.val h)

#print axioms value_unit
#print axioms value_prod
#print axioms value_monomial
#print axioms zpow_clear
#print axioms cleared_identity
#print axioms exponents_zero
#print axioms unit_eq_coefficient
end Verification.LaurentBoundaryUnits
