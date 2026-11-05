/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SevenfoldCoordinateKernel

/-!
# Sevenfold Cycle Support

The integral square generator is supported on an induced subset exactly
when that subset contains the four vertices, unless its coefficient is zero.
-/
noncomputable section
open scoped Classical
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000
namespace Verification.SevenfoldCycleSupport
open Verification.SevenfoldChainMatrix Verification.SevenfoldChainDegrees
open Verification.SevenfoldChainIndex Verification.SevenfoldCoordinateKernel

def whole (T : Finset (Fin 5)) : Prop := {0,1,2,3} ⊆ T

theorem vector_coordinates (T : Finset (Fin 5)) (a : ℤ) (h : whole T ∨ a=0) :
    vector a ∈ coordinates T (-2) := by
  rcases h with h | rfl
  · constructor
    · intro i hi
      change -((face i).card : ℤ) ≠ -2 at hi
      rw [degree_values] at hi
      fin_cases i <;> norm_num [Fin.ext_iff, Fin.le_def, Fin.coe_ofNat_eq_mod] at hi ⊢ <;> simp [vector]
    · intro i hi
      fin_cases i <;> simp [vector]
      all_goals
        exfalso
        apply hi
        exact Finset.Subset.trans (by decide) h
  · have he : vector 0=0 := by ext i; fin_cases i <;> simp [vector]
    rw [he]
    exact Submodule.zero_mem _

theorem coefficient_support (T : Finset (Fin 5)) (x : coordinates T (-2))
    (hx : Matrix.mulVec matrix x.val=0) : whole T ∨ x.val 6=0 := by
  by_cases ha : x.val 6=0
  · exact Or.inr ha
  · left
    have he := kernel_vector T x hx
    have h6 : face 6 ⊆ T := by
      by_contra hn
      have hz := x.property.2 6 hn
      rw [he] at hz
      exact ha (by simpa [vector] using hz)
    have h8 : face 8 ⊆ T := by
      by_contra hn
      have hz := x.property.2 8 hn
      rw [he] at hz
      exact ha (by simpa [vector] using hz)
    change ({0,1,2,3} : Finset (Fin 5)) ⊆ T
    rw [show ({0,1,2,3} : Finset (Fin 5)) = face 6 ∪ face 8 from by decide]
    exact Finset.union_subset h6 h8

#print axioms whole
#print axioms vector_coordinates
#print axioms coefficient_support
end Verification.SevenfoldCycleSupport
