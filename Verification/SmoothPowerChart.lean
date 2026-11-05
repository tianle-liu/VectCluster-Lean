/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PowerFibers
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Smooth Power Chart

Actual tame power charts for the original local smoothness argument in
manuscript.tex:390–408. Over any commutative base S, adjoining a root of
X^e-b is finite etale when b and e are units and e>0. We apply this to
S=k[x,y,(xy-1)^{-1}] and prove the resulting chart smooth over k.

The polynomial, localization, adjoining quotient, and scalar towers are
actual mathlib algebras. The x-coordinate map is smooth, with smooth fibers.
This does not identify the full exchange local presentation with a product
of these charts or supply its ordered normal-frame identification.
-/

noncomputable section

universe u

namespace Verification.SmoothPowerChart

section GeneralPower

variable (S : Type u) [CommRing S]

def powerPolynomial (e : ℕ) (b : Sˣ) : Polynomial S :=
  Polynomial.X ^ e - Polynomial.C (b : S)

abbrev PowerAlgebra (e : ℕ) (b : Sˣ) := AdjoinRoot (powerPolynomial S e b)

theorem power_separable (e : ℕ) (b : Sˣ) (he : IsUnit (e : S)) :
    (powerPolynomial S e b).Separable := Polynomial.separable_X_pow_sub_C_unit b he

theorem power_monic (e : ℕ) (b : Sˣ) (he : 0 < e) :
    (powerPolynomial S e b).Monic :=
  Polynomial.monic_X_pow_sub_C (b : S) (Nat.ne_of_gt he)

theorem power_finite (e : ℕ) (b : Sˣ) (he : 0 < e) :
    Module.Finite S (PowerAlgebra S e b) := (power_monic S e b he).finite_adjoinRoot

theorem power_free (e : ℕ) (b : Sˣ) (he : 0 < e) :
    Module.Free S (PowerAlgebra S e b) := (power_monic S e b he).free_adjoinRoot

theorem power_etale (e : ℕ) (b : Sˣ) (he : IsUnit (e : S)) :
    Algebra.Etale S (PowerAlgebra S e b) :=
  PowerFibers.separable_adjoinRoot_etale _ (power_separable S e b he)

theorem power_finite_etale (e : ℕ) (b : Sˣ) (hpos : 0 < e) (he : IsUnit (e : S)) :
    Module.Finite S (PowerAlgebra S e b) ∧ Algebra.Etale S (PowerAlgebra S e b) :=
  ⟨power_finite S e b hpos, power_etale S e b he⟩

def root (e : ℕ) (b : Sˣ) : PowerAlgebra S e b := AdjoinRoot.root (powerPolynomial S e b)

theorem root_power (e : ℕ) (b : Sˣ) :
    root S e b ^ e = algebraMap S (PowerAlgebra S e b) (b : S) := by
  have h := AdjoinRoot.eval₂_root (powerPolynomial S e b)
  simpa [root, powerPolynomial, sub_eq_zero] using h

theorem root_isUnit (e : ℕ) (b : Sˣ) (he : 0 < e) : IsUnit (root S e b) := by
  apply (isUnit_pow_iff (Nat.ne_of_gt he)).mp
  rw [root_power]
  exact b.isUnit.map (algebraMap S (PowerAlgebra S e b))

theorem root_derivative_isUnit (e : ℕ) (b : Sˣ) (he : IsUnit (e : S)) :
    IsUnit (Polynomial.aeval (root S e b) (powerPolynomial S e b).derivative) := by
  apply PowerFibers.derivative_unit_at_root _ (power_separable S e b he)
  simp [root]

end GeneralPower

section Chart

variable (k : Type u) [CommRing k]

abbrev Plane := MvPolynomial (Fin 2) k

def puncture : Plane k := MvPolynomial.X 0 * MvPolynomial.X 1 - 1

/-- The actual open chart D(xy-1) in the affine plane. -/
abbrev ChartBase := Localization.Away (puncture k)

def baseCoordinate (i : Fin 2) : ChartBase k :=
  algebraMap (Plane k) (ChartBase k) (MvPolynomial.X i)

theorem puncture_isUnit :
    IsUnit (algebraMap (Plane k) (ChartBase k) (puncture k)) :=
  IsLocalization.Away.algebraMap_isUnit (puncture k)

def punctureUnit : (ChartBase k)ˣ := (puncture_isUnit k).unit

theorem punctureUnit_val : (punctureUnit k : ChartBase k) =
    baseCoordinate k 0 * baseCoordinate k 1 - 1 := by
  rw [punctureUnit, IsUnit.unit_spec]
  simp only [puncture, map_sub, map_mul, map_one, baseCoordinate]

theorem plane_smooth : Algebra.Smooth k (Plane k) where
  formallySmooth := Algebra.FormallySmooth.of_equiv
    (MvPolynomial.renameEquiv k (Equiv.ulift : ULift.{u} (Fin 2) ≃ Fin 2))

theorem base_smooth : Algebra.Smooth k (ChartBase k) := by
  letI : Algebra.Smooth k (Plane k) := plane_smooth k
  letI : Algebra.Smooth (Plane k) (ChartBase k) :=
    Algebra.Smooth.of_isLocalization_Away (puncture k)
  exact Algebra.Smooth.comp k (Plane k) (ChartBase k)

/-- The quotient by z^e=(xy-1) over the actual localized plane. -/
abbrev Chart (e : ℕ) := PowerAlgebra (ChartBase k) e (punctureUnit k)

def coordinate (e : ℕ) (i : Fin 2) : Chart k e :=
  algebraMap (ChartBase k) (Chart k e) (baseCoordinate k i)

def chartRoot (e : ℕ) : Chart k e := root (ChartBase k) e (punctureUnit k)

theorem chart_equation (e : ℕ) :
    chartRoot k e ^ e = coordinate k e 0 * coordinate k e 1 - 1 := by
  rw [chartRoot, root_power, punctureUnit_val]
  simp only [map_sub, map_mul, map_one, coordinate]

theorem chart_root_unit (e : ℕ) (he : 0 < e) : IsUnit (chartRoot k e) :=
  root_isUnit (ChartBase k) e (punctureUnit k) he

theorem exponent_unit_on_base (e : ℕ) (he : IsUnit (e : k)) : IsUnit (e : ChartBase k) := by
  simpa only [map_natCast] using he.map (algebraMap k (ChartBase k))

theorem chart_etale (e : ℕ) (he : IsUnit (e : k)) :
    Algebra.Etale (ChartBase k) (Chart k e) :=
  power_etale (ChartBase k) e (punctureUnit k) (exponent_unit_on_base k e he)

theorem chart_finite (e : ℕ) (he : 0 < e) : Module.Finite (ChartBase k) (Chart k e) :=
  power_finite (ChartBase k) e (punctureUnit k) he

/-- Smoothness follows from the smooth localized plane and the etale quotient. -/
theorem chart_smooth (e : ℕ) (he : IsUnit (e : k)) : Algebra.Smooth k (Chart k e) := by
  letI : Algebra.Smooth k (ChartBase k) := base_smooth k
  letI : Algebra.Etale (ChartBase k) (Chart k e) := chart_etale k e he
  letI : Algebra.Smooth (ChartBase k) (Chart k e) := {}
  exact Algebra.Smooth.comp k (ChartBase k) (Chart k e)

open scoped TensorProduct

/-- Products of these actual charts are smooth as well. Iterating this step
handles any fixed finite collection of tame power coordinates. -/
theorem two_charts_smooth (e f : ℕ) (he : IsUnit (e : k)) (hf : IsUnit (f : k)) :
    Algebra.Smooth k (Chart k e ⊗[k] Chart k f) := by
  letI : Algebra.Smooth k (Chart k e) := chart_smooth k e he
  letI : Algebra.Smooth k (Chart k f) := chart_smooth k f hf
  exact Algebra.Smooth.comp k (Chart k e) (Chart k e ⊗[k] Chart k f)

end Chart

section CoordinateParameter

variable (k : Type u) [CommRing k]

/-- Regard the same affine plane as the polynomial line in y over k[x]. -/
def parameterPresentation : Plane k ≃ₐ[k] MvPolynomial (Fin 1) (Polynomial k) :=
  (MvPolynomial.renameEquiv k (_root_.finSuccEquiv 1)).trans
    (MvPolynomial.optionEquivRight k (Fin 1))

instance parameterAlgebra : Algebra (Polynomial k) (Plane k) :=
  ((parameterPresentation k).symm.toRingHom.comp MvPolynomial.C).toAlgebra

def parameterEquiv : MvPolynomial (Fin 1) (Polynomial k) ≃ₐ[Polynomial k] Plane k :=
  AlgEquiv.ofRingEquiv (f := (parameterPresentation k).symm.toRingEquiv) (fun _ => rfl)

theorem parameter_presentation_x :
    parameterPresentation k (MvPolynomial.X 0) = MvPolynomial.C Polynomial.X := by
  simp [parameterPresentation, MvPolynomial.optionEquivRight_X_none]

theorem parameter_algebraMap_X :
    algebraMap (Polynomial k) (Plane k) Polynomial.X = MvPolynomial.X 0 := by
  apply (parameterPresentation k).injective
  change parameterPresentation k ((parameterPresentation k).symm
    (MvPolynomial.C Polynomial.X)) = _
  rw [AlgEquiv.apply_symm_apply, parameter_presentation_x]

theorem plane_parameter_smooth : Algebra.Smooth (Polynomial k) (Plane k) := by
  letI : Algebra.Smooth (Polynomial k) (MvPolynomial (Fin 1) (Polynomial k)) := {
    formallySmooth := Algebra.FormallySmooth.of_equiv
      (MvPolynomial.renameEquiv (Polynomial k) (Equiv.ulift : ULift.{u} (Fin 1) ≃ Fin 1)) }
  exact Algebra.Smooth.of_equiv (parameterEquiv k)

theorem base_parameter_smooth : Algebra.Smooth (Polynomial k) (ChartBase k) := by
  letI : Algebra.Smooth (Polynomial k) (Plane k) := plane_parameter_smooth k
  letI : Algebra.Smooth (Plane k) (ChartBase k) :=
    Algebra.Smooth.of_isLocalization_Away (puncture k)
  exact Algebra.Smooth.comp (Polynomial k) (Plane k) (ChartBase k)

/-- The x-coordinate map from the actual power chart to the affine line is
smooth. Thus the construction retains the coordinate-parameter map, rather
than proving only abstract smoothness of its source algebra. -/
theorem chart_parameter_smooth (e : ℕ) (he : IsUnit (e : k)) :
    Algebra.Smooth (Polynomial k) (Chart k e) := by
  letI : Algebra.Smooth (Polynomial k) (ChartBase k) := base_parameter_smooth k
  letI : Algebra.Etale (ChartBase k) (Chart k e) := chart_etale k e he
  letI : Algebra.Smooth (ChartBase k) (Chart k e) := {}
  exact Algebra.Smooth.comp (Polynomial k) (ChartBase k) (Chart k e)

theorem chart_parameter_image_X (e : ℕ) :
    algebraMap (Polynomial k) (Chart k e) Polynomial.X = coordinate k e 0 := by
  rw [IsScalarTower.algebraMap_apply (Polynomial k) (Plane k) (Chart k e),
    parameter_algebraMap_X]
  rw [IsScalarTower.algebraMap_apply (Plane k) (ChartBase k) (Chart k e)]
  rfl

def parameterValueAlgebra (a : k) : Algebra (Polynomial k) k :=
  (Polynomial.evalRingHom a).toAlgebra

open scoped TensorProduct

/-- The actual base-change fiber over x=a of the proved coordinate map. -/
abbrev CoordinateFiber (e : ℕ) (a : k) :=
  letI := parameterValueAlgebra k a
  k ⊗[Polynomial k] Chart k e

/-- In particular the x=0 fiber is smooth over k. -/
theorem coordinate_fiber_smooth (e : ℕ) (he : IsUnit (e : k)) (a : k) :
    Algebra.Smooth k (CoordinateFiber k e a) := by
  letI := parameterValueAlgebra k a
  letI : Algebra.Smooth (Polynomial k) (Chart k e) := chart_parameter_smooth k e he
  exact Algebra.Smooth.baseChange (Polynomial k) (Chart k e) k

end CoordinateParameter

section Field

variable (k : Type u) [Field k]

theorem chart_smooth_of_char (p e : ℕ) [CharP k p] (he : ¬p ∣ e) :
    Algebra.Smooth k (Chart k e) := by
  apply chart_smooth k e
  apply isUnit_iff_ne_zero.mpr
  exact (CharP.cast_eq_zero_iff k p e).not.mpr he

end Field

#print axioms powerPolynomial
#print axioms PowerAlgebra
#print axioms power_separable
#print axioms power_monic
#print axioms power_finite
#print axioms power_free
#print axioms power_etale
#print axioms power_finite_etale
#print axioms root
#print axioms root_power
#print axioms root_isUnit
#print axioms root_derivative_isUnit
#print axioms Plane
#print axioms puncture
#print axioms ChartBase
#print axioms baseCoordinate
#print axioms puncture_isUnit
#print axioms punctureUnit
#print axioms punctureUnit_val
#print axioms plane_smooth
#print axioms base_smooth
#print axioms Chart
#print axioms coordinate
#print axioms chartRoot
#print axioms chart_equation
#print axioms chart_root_unit
#print axioms exponent_unit_on_base
#print axioms chart_etale
#print axioms chart_finite
#print axioms chart_smooth
#print axioms two_charts_smooth
#print axioms parameterPresentation
#print axioms parameterAlgebra
#print axioms parameterEquiv
#print axioms parameter_presentation_x
#print axioms parameter_algebraMap_X
#print axioms plane_parameter_smooth
#print axioms base_parameter_smooth
#print axioms chart_parameter_smooth
#print axioms chart_parameter_image_X
#print axioms parameterValueAlgebra
#print axioms CoordinateFiber
#print axioms coordinate_fiber_smooth
#print axioms chart_smooth_of_char

end Verification.SmoothPowerChart
