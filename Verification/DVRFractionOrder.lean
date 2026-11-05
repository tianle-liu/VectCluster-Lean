/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.GroupWithZero.WithZero

/-!
# DVR Fraction Order

The integer order of a nonzero rational function in an actual DVR.
This is constructed from mathlib's adic valuation of the maximal ideal;
it is not an independently supplied residue or order function.
-/
noncomputable section
namespace Verification.DVRFractionOrder
open scoped Multiplicative
variable (D : Type) [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
variable (K : Type) [Field K] [Algebra D K] [IsFractionRing D K]

def prime : IsDedekindDomain.HeightOneSpectrum D :=
  ⟨IsLocalRing.maximalIdeal D,inferInstance,IsDiscreteValuationRing.not_a_field D⟩

def valuation : Valuation K ℤₘ₀ := (prime D).valuation K

def order : Additive Kˣ →+ ℤ where
  toFun u := -Multiplicative.toAdd (WithZero.unitsWithZeroEquiv
    (Units.map (valuation D K).toMonoidHom (Additive.toMul u)))
  map_zero' := by simp
  map_add' := by intro a b; simp [add_comm]

theorem valuation_order (u : Kˣ) : valuation D K u =
    ((Multiplicative.ofAdd (-(order D K (Additive.ofMul u))) : Multiplicative ℤ) : ℤₘ₀) := by
  change (Units.map (valuation D K).toMonoidHom u).val = _
  rw [← WithZero.coe_unitsWithZeroEquiv_eq_units_val]
  simp only [order,AddMonoidHom.coe_mk,ZeroHom.coe_mk,neg_neg,ofAdd_toAdd]
  rfl

theorem order_eq_iff (u : Kˣ) (n : ℤ) : order D K (Additive.ofMul u) = n ↔
    valuation D K u = ((Multiplicative.ofAdd (-n) : Multiplicative ℤ) : ℤₘ₀) := by
  rw [valuation_order,WithZero.coe_inj]
  change _ ↔ -(order D K (Additive.ofMul u)) = -n
  exact neg_inj.symm

theorem valuation_parameter (t : D) (ht : t ≠ 0)
    (hgen : IsLocalRing.maximalIdeal D = Ideal.span {t}) :
    valuation D K (algebraMap D K t) = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : ℤₘ₀) := by
  exact ((prime D).valuation_of_algebraMap t).trans
    ((prime D).intValuation_singleton ht hgen)

theorem valuation_not_mem (a : D) (ha : a ∉ IsLocalRing.maximalIdeal D) :
    valuation D K (algebraMap D K a) = 1 := by
  rw [valuation,(prime D).valuation_of_algebraMap]
  apply le_antisymm ((prime D).intValuation_le_one a)
  apply le_of_not_gt
  intro h
  have hm := ((prime D).intValuation_lt_one_iff_dvd a).mp h
  exact ha ((Ideal.dvd_span_singleton).mp hm)

variable {A : Type} [CommRing A] (t : A) (f : A →+* D) (ht : f t ≠ 0)

def openMap : Localization.Away t →+* K :=
  IsLocalization.Away.lift t (S := Localization.Away t)
    (g := (algebraMap D K).comp f)
    (isUnit_iff_ne_zero.mpr (by
      change algebraMap D K (f t) ≠ 0
      simpa only [map_zero] using (IsFractionRing.injective D K).ne ht))

omit [IsDomain D] [IsDiscreteValuationRing D] in
theorem openMap_algebraMap (a : A) :
    openMap D K t f ht (algebraMap A (Localization.Away t) a) = algebraMap D K (f a) :=
  IsLocalization.Away.lift_eq _ _ _

def openOrder : Additive (Localization.Away t)ˣ →+ ℤ where
  toFun u := order D K (Additive.ofMul (Units.map (openMap D K t f ht).toMonoidHom
    (Additive.toMul u)))
  map_zero' := by simp
  map_add' := by intro a b; simp [add_comm]

theorem openOrder_not_mem (u : (Localization.Away t)ˣ) (a : A)
    (hu : (u : Localization.Away t) = algebraMap A (Localization.Away t) a)
    (ha : f a ∉ IsLocalRing.maximalIdeal D) :
    openOrder D K t f ht (Additive.ofMul u) = 0 := by
  change order D K (Additive.ofMul (Units.map (openMap D K t f ht).toMonoidHom u)) = 0
  apply (order_eq_iff D K _ 0).mpr
  change valuation D K (openMap D K t f ht (u : Localization.Away t)) = _
  rw [hu,openMap_algebraMap,valuation_not_mem D K (f a) ha]
  rfl

/-- Only equality of the actual images in the fraction field is required. -/
theorem openOrder_of_image_parameter (u : (Localization.Away t)ˣ)
    (hu : openMap D K t f ht (u : Localization.Away t) = algebraMap D K (f t))
    (hgen : IsLocalRing.maximalIdeal D = Ideal.span {f t}) :
    openOrder D K t f ht (Additive.ofMul u) = 1 := by
  change order D K (Additive.ofMul (Units.map (openMap D K t f ht).toMonoidHom u)) = 1
  apply (order_eq_iff D K _ 1).mpr
  change valuation D K (openMap D K t f ht (u : Localization.Away t)) = _
  rw [hu]
  exact valuation_parameter D K (f t) ht hgen

theorem openOrder_parameter (u : (Localization.Away t)ˣ)
    (hu : (u : Localization.Away t) = algebraMap A (Localization.Away t) t)
    (hgen : IsLocalRing.maximalIdeal D = Ideal.span {f t}) :
    openOrder D K t f ht (Additive.ofMul u) = 1 := by
  change order D K (Additive.ofMul (Units.map (openMap D K t f ht).toMonoidHom u)) = 1
  apply (order_eq_iff D K _ 1).mpr
  change valuation D K (openMap D K t f ht (u : Localization.Away t)) = _
  rw [hu,openMap_algebraMap]
  exact valuation_parameter D K (f t) ht hgen

theorem openOrder_zpow (u : (Localization.Away t)ˣ) (n : ℤ) :
    openOrder D K t f ht (Additive.ofMul (u ^ n)) =
      n * openOrder D K t f ht (Additive.ofMul u) := by
  change openOrder D K t f ht (n • Additive.ofMul u) = _
  simp only [map_zsmul,zsmul_eq_mul,Int.cast_id]

#print axioms prime
#print axioms valuation
#print axioms order
#print axioms valuation_order
#print axioms order_eq_iff
#print axioms valuation_parameter
#print axioms valuation_not_mem
#print axioms openMap
#print axioms openMap_algebraMap
#print axioms openOrder
#print axioms openOrder_not_mem
#print axioms openOrder_of_image_parameter
#print axioms openOrder_parameter
#print axioms openOrder_zpow
end Verification.DVRFractionOrder
