/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Finite Matrix Row Splitting

Integral row generation is equivalent to an actual left inverse of
the full column map. This provides a direct RFR interface for mutation.
-/
noncomputable section
namespace Verification.FiniteMatrixRowSplitting
open Classical
variable {V F : Type} [Fintype V] [Fintype F]
variable (B : Matrix F V ℤ)

def RFR : Prop := Function.Surjective B.transpose.mulVecLin

def leftMatrix (h : RFR B) : Matrix V F ℤ := fun i=>Classical.choose (h (Pi.single i 1))

omit [Fintype V] in
theorem left_matrix (h : RFR B) : leftMatrix B h*B=1 := by
  ext i j
  have hh := congrFun (Classical.choose_spec (h (Pi.single i 1))) j
  change (∑r,B r j*Classical.choose (h (Pi.single i 1)) r)= (Pi.single i (1:ℤ) : V→ℤ) j at hh
  simpa only [Matrix.mul_apply,leftMatrix,Matrix.one_apply,Pi.single_apply,eq_comm,mul_comm] using hh

def retraction (h : RFR B) : (F→ℤ)→ₗ[ℤ](V→ℤ) := (leftMatrix B h).mulVecLin

theorem left (h : RFR B) : (retraction B h).comp B.mulVecLin=LinearMap.id := by
  rw [retraction,←Matrix.mulVecLin_mul,left_matrix,Matrix.mulVecLin_one]

theorem rows_of_left (r : (F→ℤ)→ₗ[ℤ](V→ℤ)) (hr : r.comp B.mulVecLin=LinearMap.id) : RFR B := by
  have hm : LinearMap.toMatrix' r*B=1 := by
    have hh := congrArg LinearMap.toMatrix' hr
    rw [LinearMap.toMatrix'_comp,LinearMap.toMatrix'_id] at hh
    have hb := LinearMap.toMatrix'_toLin' B
    change LinearMap.toMatrix' B.mulVecLin=B at hb
    rwa [hb] at hh
  intro x
  refine ⟨(LinearMap.toMatrix' r).transpose.mulVec x,?_⟩
  change B.transpose.mulVec ((LinearMap.toMatrix' r).transpose.mulVec x)=x
  rw [Matrix.mulVec_mulVec,←Matrix.transpose_mul,hm,Matrix.transpose_one,Matrix.one_mulVec]

#print axioms RFR
#print axioms leftMatrix
#print axioms left_matrix
#print axioms retraction
#print axioms left
#print axioms rows_of_left
end Verification.FiniteMatrixRowSplitting
