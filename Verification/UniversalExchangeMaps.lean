/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.UniversalExchangeChart

/-!
# Universal Exchange Maps

Universal maps from the actual open polynomial exchange model. These
maps retain the coefficient algebra and both displayed coordinates.
-/
noncomputable section
namespace Verification.UniversalExchangeMaps
open MvPolynomial Verification.UniversalExchangeChart
variable {R A B ι : Type} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]
attribute [local instance] MvPolynomial.algebraMvPolynomial

def x (A ι : Type) [CommRing A] (i : ι) : OpenPolynomial A ι :=
  algebraMap (Polynomial A ι) (OpenPolynomial A ι) (X (Sum.inl i))
def y (A ι : Type) [CommRing A] (i : ι) : OpenPolynomial A ι :=
  algebraMap (Polynomial A ι) (OpenPolynomial A ι) (X (Sum.inr i))

theorem determinant_unit (A ι : Type) [CommRing A] (i : ι) :
    IsUnit (x A ι i * y A ι i - 1) := by
  have h := (valueUnit A ι i).isUnit
  rw [valueUnit_val] at h
  simpa only [value, map_sub, map_mul, map_one, x, y] using h

def polynomialMap (f : A →ₐ[R] B) (xx yy : ι → B) : Polynomial A ι →ₐ[R] B :=
  aevalTower f (Sum.elim xx yy)

theorem polynomialMap_units (f : A →ₐ[R] B) (xx yy : ι → B)
    (h : ∀ i, IsUnit (xx i * yy i - 1))
    (m : SplitExchangeChart.valueMonoid (value A ι)) :
    IsUnit (polynomialMap f xx yy m) := by
  apply SplitExchangeChart.units_on_closure (polynomialMap f xx yy).toRingHom (value A ι) _ m
  intro i
  change IsUnit (aevalTower f (Sum.elim xx yy) (value A ι i))
  simpa only [value, map_sub, map_mul, map_one, aevalTower_X,
    Sum.elim_inl, Sum.elim_inr] using h i

def lift (f : A →ₐ[R] B) (xx yy : ι → B) (h : ∀ i, IsUnit (xx i * yy i - 1)) :
    OpenPolynomial A ι →ₐ[R] B := IsLocalization.liftAlgHom (polynomialMap_units f xx yy h)

@[simp] theorem lift_x (f : A →ₐ[R] B) (xx yy : ι → B)
    (h : ∀ i, IsUnit (xx i * yy i - 1)) (i : ι) : lift f xx yy h (x A ι i) = xx i := by
  change IsLocalization.lift (polynomialMap_units f xx yy h) (algebraMap _ _ (X (Sum.inl i))) = _
  rw [IsLocalization.lift_eq]
  exact aevalTower_X _ _ _

@[simp] theorem lift_y (f : A →ₐ[R] B) (xx yy : ι → B)
    (h : ∀ i, IsUnit (xx i * yy i - 1)) (i : ι) : lift f xx yy h (y A ι i) = yy i := by
  change IsLocalization.lift (polynomialMap_units f xx yy h) (algebraMap _ _ (X (Sum.inr i))) = _
  rw [IsLocalization.lift_eq]
  exact aevalTower_X _ _ _

@[simp] theorem lift_coefficient (f : A →ₐ[R] B) (xx yy : ι → B)
    (h : ∀ i, IsUnit (xx i * yy i - 1)) (a : A) :
    lift f xx yy h (algebraMap A (OpenPolynomial A ι) a) = f a := by
  rw [IsScalarTower.algebraMap_apply A (Polynomial A ι) (OpenPolynomial A ι)]
  change IsLocalization.lift (polynomialMap_units f xx yy h) (algebraMap _ _ (C a)) = _
  rw [IsLocalization.lift_eq]
  exact aevalTower_C _ _ _

theorem hom_ext (f g : OpenPolynomial A ι →ₐ[R] B)
    (hc : ∀ a, f (algebraMap A _ a) = g (algebraMap A _ a))
    (hx : ∀ i, f (x A ι i) = g (x A ι i))
    (hy : ∀ i, f (y A ι i) = g (y A ι i)) : f = g := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (SplitExchangeChart.valueMonoid (value A ι))
  apply MvPolynomial.ringHom_ext
  · exact hc
  · intro v
    cases v with
    | inl i => exact hx i
    | inr i => exact hy i

#print axioms x
#print axioms y
#print axioms determinant_unit
#print axioms polynomialMap
#print axioms polynomialMap_units
#print axioms lift
#print axioms lift_x
#print axioms lift_y
#print axioms lift_coefficient
#print axioms hom_ext
end Verification.UniversalExchangeMaps
