/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathRightClosedRecursion

/-!
# Path Endpoint Recursion Constants

The actual normalized endpoint constants under deletion of two path vertices.
-/

namespace Verification.PathEndpointRecursionConstants

open Verification.PathEndpointComplex Verification.PathAffineLeftEndpoint Verification.PathAffineRightEndpoint

variable {R : Type*} [CommRing R] (g ρ : R)

theorem signAt_all (i : ℕ) : signAt true true i=true := by
  rw [signAt_parity]
  simp

theorem signAt_even_right (a b : Bool) (m : ℕ) : signAt a b (2*m+1)=b := by
  rw [signAt_parity]
  have he : (2*m+1)%2 ≠ 0 := by omega
  simp only [he,↓reduceIte]

theorem endpoint_two_step (hr : (1+g)*ρ=0) (n : ℕ) :
    flipConstant g ρ true (endpointConstant ρ (n+2))=endpointConstant ρ n := by
  have hq : (n+2+1)/2=(n+1)/2+1 := by omega
  by_cases he : ((n+1)/2)%2=0
  · have hn : ((n+2+1)/2)%2 ≠ 0 := by omega
    simp only [endpointConstant,he,hn,↓reduceIte,flipConstant]
    linear_combination hr
  · have hn : ((n+2+1)/2)%2=0 := by omega
    simp only [endpointConstant,he,hn,↓reduceIte,flipConstant,mul_zero,add_zero]

theorem z_source_constant (hr : (1+g)*ρ=0) (n : ℕ) :
    flipConstant g ρ (signAt true true (n+1)) (endpointConstant ρ (n+2))=endpointConstant ρ n := by
  rw [signAt_all,endpoint_two_step g ρ hr]

theorem y_source_right_constant (hr : (1+g)*ρ=0) (m : ℕ) :
    flipConstant g ρ (signAt false true (2*m+1)) (endpointConstant ρ (2*m+2))=
      endpointConstant ρ (2*m) := by
  rw [signAt_even_right,endpoint_two_step g ρ hr]

theorem y_source_left_constant : flipConstant g ρ false 0=0 := rfl

#print axioms signAt_all
#print axioms signAt_even_right
#print axioms endpoint_two_step
#print axioms z_source_constant
#print axioms y_source_right_constant
#print axioms y_source_left_constant

end Verification.PathEndpointRecursionConstants
