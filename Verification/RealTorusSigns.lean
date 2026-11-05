/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RealOrthants
import Verification.DiscreteFiberComponents
import Mathlib.Topology.Constructions

/-!
# Real Torus Signs

The sign map on the actual real torus is continuous; its actual fibers
are the logarithmic orthants. This identifies connected components.
-/
noncomputable section
namespace Verification.RealTorusSigns
open Verification.RealOrthants
variable {κ : Type*}

def Torus (κ : Type*) := {x : κ → ℝ // ∀ a, x a ≠ 0}

instance torusTopology : TopologicalSpace (Torus κ) :=
  inferInstanceAs (TopologicalSpace {x : κ → ℝ // ∀ a, x a ≠ 0})

def signs (x : Torus κ) : κ → Bool := fun a => decide (x.val a<0)

theorem signs_continuous : Continuous (signs : Torus κ → κ → Bool) := by
  apply continuous_pi
  intro a
  rw [continuous_bool_rng true]
  change IsClopen {x : Torus κ | decide (x.val a<0)=true}
  simp only [decide_eq_true_eq]
  have hc : Continuous (fun x : Torus κ => x.val a) :=
    (continuous_apply a).comp continuous_subtype_val
  constructor
  · have he : {x : Torus κ | x.val a<0}={x : Torus κ | x.val a≤0} := by
      ext x
      exact lt_iff_le_and_ne.trans (and_iff_left (x.property a))
    rw [he]
    exact isClosed_le hc continuous_const
  · exact isOpen_lt hc continuous_const

theorem signs_condition (x : Torus κ) (a : κ) :
    if signs x a then x.val a<0 else 0<x.val a := by
  by_cases h : x.val a<0
  · simp [signs,h]
  · simp only [signs,h,decide_false,Bool.false_eq_true,if_false]
    exact lt_of_le_of_ne (le_of_not_gt h) (Ne.symm (x.property a))

def fiberToOrthant (σ : κ → Bool) (x : {x : Torus κ // signs x=σ}) : orthant σ :=
  ⟨x.val.val,fun a => by
    have h := signs_condition x.val a
    rwa [x.property] at h⟩

def orthantToFiber (σ : κ → Bool) (x : orthant σ) : {x : Torus κ // signs x=σ} :=
  ⟨⟨x.val,fun a => coordinate_ne_zero σ x a⟩,by
    funext a
    have hx := x.property a
    cases h : σ a
    · simp only [h,Bool.false_eq_true,if_false] at hx
      simp [signs,not_lt.mpr hx.le,h]
    · simp only [h,if_true] at hx
      simp [signs,hx,h]⟩

def fiberEquiv (σ : κ → Bool) : {x : Torus κ // signs x=σ} ≃ₜ orthant σ where
  toFun := fiberToOrthant σ
  invFun := orthantToFiber σ
  left_inv x := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

theorem fiber_contractible (σ : κ → Bool) : ContractibleSpace {x : Torus κ // signs x=σ} := by
  letI := Verification.RealOrthants.contractible σ
  exact (fiberEquiv σ).contractibleSpace

theorem signs_surjective : Function.Surjective (signs : Torus κ → κ → Bool) := by
  intro σ
  let x := (logCoordinates σ).symm 0
  let y := (fiberEquiv σ).symm x
  exact ⟨y.val,y.property⟩

def componentsEquiv : ConnectedComponents (Torus κ) ≃ (κ → Bool) := by
  apply Verification.DiscreteFiberComponents.componentsEquiv signs signs_continuous _ signs_surjective
  intro σ
  letI := fiber_contractible σ
  infer_instance

theorem card_components [Fintype κ] : Nat.card (ConnectedComponents (Torus κ))=2^Fintype.card κ := by
  classical
  rw [Nat.card_congr (componentsEquiv (κ := κ))]
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool]

#print axioms Torus
#print axioms torusTopology
#print axioms signs
#print axioms signs_continuous
#print axioms signs_condition
#print axioms fiberToOrthant
#print axioms orthantToFiber
#print axioms fiberEquiv
#print axioms fiber_contractible
#print axioms signs_surjective
#print axioms componentsEquiv
#print axioms card_components
end Verification.RealTorusSigns
