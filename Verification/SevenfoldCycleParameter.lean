/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SevenfoldActualCycles

/-!
# Sevenfold Cycle Parameter

A genuine one-parameter integral kernel, with induced-subset support
recorded rather than assumed.
-/
noncomputable section
open scoped Classical
namespace Verification.SevenfoldCycleParameter
open Verification.SevenfoldCoordinateKernel Verification.SevenfoldCycleSupport
open Verification.SevenfoldActualCycles
variable (T : Finset (Fin 5))

def parameters : Submodule ℤ ℤ where
  carrier := {a | whole T ∨ a=0}
  zero_mem' := Or.inr rfl
  add_mem' := by
    intro a b ha hb
    by_cases h : whole T
    · exact Or.inl h
    · exact Or.inr (by rw [ha.resolve_left h,hb.resolve_left h,add_zero])
  smul_mem' := by
    intro r a ha
    by_cases h : whole T
    · exact Or.inl h
    · exact Or.inr (by rw [ha.resolve_left h,smul_zero])

def equiv : LinearMap.ker (coordinateDelta T) ≃ₗ[ℤ] parameters T where
  toFun x := ⟨x.val.val 6,coefficient_support T x.val x.property⟩
  invFun a := ⟨⟨vector a.val,vector_coordinates T a.val a.property⟩,vector_cycle a.val⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact (kernel_vector T x.val x.property).symm
  right_inv a := by apply Subtype.ext; rfl
  map_add' x y := by apply Subtype.ext; rfl
  map_smul' r x := by apply Subtype.ext; rfl

theorem top (h : whole T) : parameters T=⊤ := by
  ext a
  simp only [parameters,Submodule.mem_mk,Set.mem_setOf_eq,Submodule.mem_top,iff_true]
  exact Or.inl h

theorem bot (h : ¬whole T) : parameters T=⊥ := by
  ext a
  change (whole T ∨ a=0) ↔ a=0
  simp [h]

#print axioms parameters
#print axioms equiv
#print axioms top
#print axioms bot
end Verification.SevenfoldCycleParameter
