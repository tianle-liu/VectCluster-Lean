/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SevenfoldChainCoordinates

/-!
# Sevenfold Chain Degrees

Actual homogeneous chain terms in the ten-face coordinates, retaining
both the induced-subset support and the original cardinality degree.
-/
noncomputable section
open scoped Classical
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000
namespace Verification.SevenfoldChainDegrees
open Verification.SevenfoldGraphFreeness Verification.SevenfoldChainIndex
open Verification.SevenfoldChainCoordinates Verification.GraphCover
open Verification.GraphCoverGrading Verification.GradedPerturbation
variable (T : Finset (Fin 5))

def supported : Submodule ℤ (Fin 10 → ℤ) where
  carrier := {x | ∀ i, ¬face i ⊆ T → x i=0}
  zero_mem' := by simp
  add_mem' hx hy := by intro i hi; simp [hx i hi,hy i hi]
  smul_mem' r x hx := by intro i hi; simp [hx i hi]

def coordinates (p : ℤ) : Submodule ℤ (Fin 10 → ℤ) :=
  degreeModule (fun i => -(face i).card) p ⊓ supported T

def term (p : ℤ) : degreeModule (R := ℤ) (degree graph T) p ≃ₗ[ℤ] coordinates T p where
  toFun f := ⟨extend T f.val,by
    constructor
    · intro i hi
      by_cases hs : face i ⊆ T
      · rw [extend_index T f.val ⟨i,hs⟩]
        apply f.property
        simpa only [degree,index_face] using hi
      · simp [extend,hs]
    · intro i hi
      simp [extend,hi]⟩
  invFun x := ⟨fun J => x.val ((index T).symm J).val,by
    intro J hJ
    apply x.property.1
    have hface : face ((index T).symm J).val = J.val := by
      rw [← index_face,Equiv.apply_symm_apply]
    simpa only [hface,degree] using hJ⟩
  left_inv f := by
    apply Subtype.ext
    funext J
    change extend T f.val ((index T).symm J).val = f.val J
    rw [extend_index,Equiv.apply_symm_apply]
  right_inv x := by
    apply Subtype.ext
    funext i
    by_cases hi : face i ⊆ T
    · simp [extend,hi]
    · simp [extend,hi,x.property.2 i hi]
  map_add' f g := by apply Subtype.ext; exact map_add (extend T) f.val g.val
  map_smul' r f := by apply Subtype.ext; exact map_smul (extend T) r f.val

theorem term_value (p : ℤ) (f : degreeModule (R := ℤ) (degree graph T) p) :
    (term T p f).val = extend T f.val := rfl

theorem degree_values : ∀ i : Fin 10,
    (-(face i).card : ℤ) = if i=0 then 0 else if i≤5 then -1 else -2 := by decide

#print axioms supported
#print axioms coordinates
#print axioms term
#print axioms term_value
#print axioms degree_values
end Verification.SevenfoldChainDegrees
