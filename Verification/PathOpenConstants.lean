/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathEndpointRecursionConstants

/-!
# Path Open Constants

Actual constant symbols under deletion of one vertex and its alternating
coordinate-sign normalization.
-/

namespace Verification.PathOpenConstants

open Verification.PathEndpointComplex Verification.PathAffineLeftEndpoint Verification.PathAffineRightEndpoint

variable {R : Type*} [CommRing R] (g ρ : R)

theorem endpoint_one_step (hr : (1+g)*ρ=0) (n : ℕ) :
    flipConstant g ρ (signAt false true (n+1)) (endpointConstant ρ (n+1))=endpointConstant ρ n := by
  rw [signAt_parity]
  by_cases he : (n+1)%2=0
  · have hq : (n+1+1)/2=(n+1)/2 := by omega
    simp only [he,↓reduceIte,flipConstant,endpointConstant,hq,Bool.false_eq_true]
  · have hq : (n+1+1)/2=(n+1)/2+1 := by omega
    simp only [he,↓reduceIte,flipConstant]
    by_cases hf : ((n+1)/2)%2=0
    · have hn : ((n+1+1)/2)%2 ≠ 0 := by omega
      simp only [endpointConstant,hf,hn,↓reduceIte]
      linear_combination hr
    · have hn : ((n+1+1)/2)%2=0 := by omega
      simp only [endpointConstant,hf,hn,↓reduceIte,mul_zero,add_zero]

#print axioms endpoint_one_step

end Verification.PathOpenConstants
