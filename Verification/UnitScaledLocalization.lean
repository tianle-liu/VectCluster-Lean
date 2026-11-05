/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.RingTheory.Localization.Basic

/-!
# Unit Scaled Localization

An algebra equivalence multiplying the chosen localization generators
by units extends to their localizations. This permits frozen coordinates
alone to be inverted after a global polynomial coordinate scaling.
-/
noncomputable section
namespace Verification.UnitScaledLocalization
variable {R A B κ : Type*} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]

def monoid (x : κ → A) : Submonoid A := Submonoid.closure (Set.range x)
abbrev Loc (x : κ → A) := Localization (monoid x)

theorem generator_unit (x : κ → A) (k : κ) : IsUnit (algebraMap A (Loc x) (x k)) :=
  IsLocalization.map_units (Loc x) (⟨x k,Submonoid.subset_closure (Set.mem_range_self k)⟩ : monoid x)

variable (e : A ≃ₐ[R] B) (x : κ → A) (y : κ → B) (u : κ → Bˣ)
variable (h : ∀ k,e (x k)=(u k : B)*y k)

def coefficient : A →ₐ[R] Loc y := (IsScalarTower.toAlgHom R B (Loc y)).comp e.toAlgHom

include h in
theorem coefficient_units (z : monoid x) : IsUnit (coefficient e y z) := by
  have hh : monoid x ≤ (IsUnit.submonoid (Loc y)).comap (coefficient e y).toMonoidHom := by
    apply Submonoid.closure_le.mpr
    rintro z ⟨k,rfl⟩
    change IsUnit (algebraMap B (Loc y) (e (x k)))
    rw [h,map_mul]
    exact ((u k).isUnit.map _).mul (generator_unit y k)
  exact hh z.property

def hom : Loc x →ₐ[R] Loc y := IsLocalization.liftAlgHom (coefficient_units e x y u h)

theorem hom_algebraMap (z : A) : hom e x y u h (algebraMap A (Loc x) z)=
    algebraMap B (Loc y) (e z) := by
  change IsLocalization.lift (coefficient_units e x y u h) (algebraMap A (Loc x) z)=_
  rw [IsLocalization.lift_eq]
  rfl

def inverseUnits (k : κ) : Aˣ := Units.map e.symm.toMonoidHom (u k)⁻¹

include h in
theorem inverse_equation (k : κ) : e.symm (y k)=(inverseUnits e u k : A)*x k := by
  apply e.injective
  rw [e.apply_symm_apply,map_mul,h]
  have hu : e (inverseUnits e u k : A)=((u k)⁻¹ : Bˣ) := e.apply_symm_apply _
  rw [hu]
  simp only [← mul_assoc,Units.inv_mul,mul_one,one_mul]

theorem hom_inverse_comp : (hom e.symm y x (inverseUnits e u) (inverse_equation e x y u h)).comp
    (hom e x y u h)=AlgHom.id R (Loc x) := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (monoid x)
  apply RingHom.ext
  intro z
  change hom e.symm y x (inverseUnits e u) (inverse_equation e x y u h)
    (hom e x y u h (algebraMap A (Loc x) z))=algebraMap A (Loc x) z
  rw [hom_algebraMap,hom_algebraMap,e.symm_apply_apply]

theorem inverse_hom_comp : (hom e x y u h).comp
    (hom e.symm y x (inverseUnits e u) (inverse_equation e x y u h))=AlgHom.id R (Loc y) := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (monoid y)
  apply RingHom.ext
  intro z
  change hom e x y u h
    (hom e.symm y x (inverseUnits e u) (inverse_equation e x y u h) (algebraMap B (Loc y) z))=
      algebraMap B (Loc y) z
  rw [hom_algebraMap,hom_algebraMap,e.apply_symm_apply]

def equiv : Loc x ≃ₐ[R] Loc y :=
  AlgEquiv.ofAlgHom (hom e x y u h)
    (hom e.symm y x (inverseUnits e u) (inverse_equation e x y u h))
      (inverse_hom_comp e x y u h) (hom_inverse_comp e x y u h)

theorem equiv_algebraMap (z : A) : equiv e x y u h (algebraMap A (Loc x) z)=
    algebraMap B (Loc y) (e z) := hom_algebraMap e x y u h z

#print axioms monoid
#print axioms Loc
#print axioms generator_unit
#print axioms coefficient
#print axioms coefficient_units
#print axioms hom
#print axioms hom_algebraMap
#print axioms inverseUnits
#print axioms inverse_equation
#print axioms hom_inverse_comp
#print axioms inverse_hom_comp
#print axioms equiv
#print axioms equiv_algebraMap
end Verification.UnitScaledLocalization
