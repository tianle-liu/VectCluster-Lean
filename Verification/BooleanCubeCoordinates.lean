/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.BooleanAffineLattice

/-!
# Boolean Cube Coordinates

Exact comparison of the subset and vector presentations of a Boolean
cube, for transporting the integral signature lattice along affine maps.
-/
noncomputable section
namespace Verification.BooleanCubeCoordinates
open Verification.BooleanAffineLattice
variable {α β γ : Type*} [Fintype α] [DecidableEq α]

def cubeEquiv : Finset α ≃ (α → Bit) where
  toFun := vector
  invFun x := Finset.univ.filter (fun a => x a=1)
  left_inv S := by ext a; simp [vector]
  right_inv x := by
    funext a
    simp only [vector,Finset.mem_filter,Finset.mem_univ,true_and]
    generalize x a=b
    fin_cases b <;> norm_num

variable [Fintype β] [DecidableEq β]

theorem asFinset_eq (F : (α → Bit) →ᵃ[Bit] (β → Bit)) (S : Finset α) :
    asFinset F S=cubeEquiv.symm (F (cubeEquiv S)) := rfl

omit [Fintype α] in
theorem vector_asFinset (F : (α → Bit) →ᵃ[Bit] (β → Bit)) (S : Finset α) :
    vector (asFinset F S)=F (vector S) :=
  cubeEquiv.apply_symm_apply _

variable [Fintype γ] [DecidableEq γ]

theorem asFinset_comp (F : (α → Bit) →ᵃ[Bit] (β → Bit))
    (G : (β → Bit) →ᵃ[Bit] (γ → Bit)) (S : Finset α) :
    asFinset G (asFinset F S)=asFinset (G.comp F) S := by
  simp only [asFinset_eq,cubeEquiv.apply_symm_apply,AffineMap.comp_apply]

theorem asFinset_left_inverse (F : (α → Bit) →ᵃ[Bit] (β → Bit))
    (G : (β → Bit) →ᵃ[Bit] (α → Bit)) (h : Function.LeftInverse G F) :
    Function.LeftInverse (asFinset G) (asFinset F) := by
  intro S
  simp only [asFinset_eq,cubeEquiv.apply_symm_apply]
  rw [h (cubeEquiv S),cubeEquiv.symm_apply_apply]

#print axioms cubeEquiv
#print axioms asFinset_eq
#print axioms vector_asFinset
#print axioms asFinset_comp
#print axioms asFinset_left_inverse
end Verification.BooleanCubeCoordinates
