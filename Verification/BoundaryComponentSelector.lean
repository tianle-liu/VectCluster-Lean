/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ReducedBoundaryBranchOrder
import Mathlib.Tactic.Ring

/-!
# Boundary Component Selector

A component idempotent which extends across a principal boundary gives
an actual unit on the open complement: it is the parameter on that component
and one on the others. Its branch orders are proved from the actual DVRs.
-/
noncomputable section
namespace Verification.BoundaryComponentSelector
variable {A : Type*} [CommRing A]

def element (a x : A) : A := 1 - a + a * x

theorem inverse_identity (a x y : A) (ha : a * a = a) (hxy : x * y = 1) :
    element a x * element a y = 1 := by
  calc
    element a x * element a y =
      1 - 2 * a + a * a + (a - a * a) * (x + y) + (a * a) * (x * y) := by
        unfold element
        ring
    _ = 1 := by rw [ha, hxy]; ring

def unit (a : A) (ha : a * a = a) (x : Aˣ) : Aˣ where
  val := element a x
  inv := element a (↑(x⁻¹))
  val_inv := inverse_identity a x (↑(x⁻¹)) ha x.val_inv
  inv_val := inverse_identity a (↑(x⁻¹)) x ha x.inv_val

theorem unit_val (a : A) (ha : a * a = a) (x : Aˣ) :
    ↑(unit a ha x) = element a (x : A) := rfl

theorem map_element {B : Type*} [CommRing B] (f : A →+* B) (a x : A) :
    f (element a x) = element (f a) (f x) := by simp only [element, map_add, map_sub, map_one, map_mul]

theorem isUnit_on_open (a x : A) (ha : a * a = a) :
    IsUnit (algebraMap A (Localization.Away x) (element a x)) := by
  let f := algebraMap A (Localization.Away x)
  obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away x) x
  have hf : f a * f a = f a := by rw [← map_mul, ha]
  refine ⟨unit (f a) hf u, ?_⟩
  change element (f a) (u : Localization.Away x) = f (element a x)
  rw [hu, map_element]

variable (A) (x : A) {J : Type*} (D : J → Type*)
variable [∀ j, CommRing (D j)] [∀ j, IsDomain (D j)]
variable (e : (A ⧸ Ideal.span {x}) ≃+* ∀ j, D j) (j : J)
open Verification.ReducedBoundaryBranchOrder

omit [∀ j, IsDomain (D j)] in
theorem projection_parameter : projection A x D e j x = 0 :=
  parameter_mem A x D e j

omit [∀ j, IsDomain (D j)] in
theorem projection_element (a : A) :
    projection A x D e j (element a x) = 1 - projection A x D e j a := by
  rw [map_element, element, projection_parameter, mul_zero, add_zero]

variable [IsNoetherianRing A] (hx : IsSMulRegular A x)

theorem order_zero (a : A) (ha : projection A x D e j a = 0) :
    order A x D e j hx (element a x) = 0 := by
  apply order_not_mem
  change projection A x D e j (element a x) ≠ 0
  rw [projection_element, ha, sub_zero]
  exact one_ne_zero

omit [IsNoetherianRing A] in
theorem local_idempotent_one (a : A) (ha : a * a = a)
    (hp : projection A x D e j a ≠ 0) :
    algebraMap A (Localization.AtPrime (branch A x D e j)) a = 1 := by
  let L := Localization.AtPrime (branch A x D e j)
  let f := algebraMap A L
  have hu : IsUnit (f a) := IsLocalization.map_units L
    (⟨a, hp⟩ : (branch A x D e j).primeCompl)
  apply hu.mul_left_cancel
  rw [← map_mul, ha, mul_one]

theorem order_one (a : A) (ha : a * a = a)
    (hp : projection A x D e j a ≠ 0) :
    order A x D e j hx (element a x) = 1 := by
  letI := localDomain A x D e j hx
  letI := discreteValuation A x D e j hx
  have h := local_idempotent_one A x D e j a ha hp
  have hv : order A x D e j hx (element a x) = order A x D e j hx x := by
    change IsDiscreteValuationRing.addVal _ _ = IsDiscreteValuationRing.addVal _ _
    congr 1
    rw [map_element, element, h, sub_self, zero_add, one_mul]
  exact hv.trans (order_parameter A x D e j hx)

theorem order_indicator (a : A) (ha : a * a = a) :
    order A x D e j hx (element a x) =
      @ite ℕ∞ (projection A x D e j a = 0) (Classical.propDecidable _) 0 1 := by
  classical
  split_ifs with hp
  · exact order_zero A x D e j hx a hp
  · exact order_one A x D e j hx a ha hp

#print axioms element
#print axioms inverse_identity
#print axioms unit
#print axioms unit_val
#print axioms map_element
#print axioms isUnit_on_open
#print axioms projection_parameter
#print axioms projection_element
#print axioms order_zero
#print axioms local_idempotent_one
#print axioms order_one
#print axioms order_indicator
end Verification.BoundaryComponentSelector
