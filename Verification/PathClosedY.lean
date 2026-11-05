/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathClosedDataTransport

/-!
# Path Closed Y

Actual Y closed recursion with its manuscript endpoint constants and
odd-coordinate affine signs.
-/

namespace Verification.PathClosedY

open Classical Verification.PathEndpointComplex Verification.PathEndpointRecursionConstants
  Verification.PathEndpointClosedData
  Verification.PathClosedDataTransport

variable {R : Type*} [CommRing R] (g ρ : R)

noncomputable def data (hg : g*g=1) (hr : (1+g)*ρ=0) (m : ℕ) :
    ClosedData (R := R) (M := YModule ρ m) (N := YModule ρ (m+1))
      (yDifferential g ρ m) (yDifferential g ρ (m+1))
      (bothSupport 0 (endpointConstant ρ (2*(m+1))) (2*(m+1))) :=
  bothSourceSize g ρ hg hr false true 0 (endpointConstant ρ (2*m)) 0
    (endpointConstant ρ (2*(m+1))) m (2*(m+1)) (by omega)
      (by simp) (by simp) (endpointConstant_relation ρ (2*(m+1))) rfl
        (by simpa only [Nat.mul_add,Nat.mul_one] using y_source_right_constant g ρ hr m)

noncomputable def closedMap (hg : g*g=1) (hr : (1+g)*ρ=0) (m : ℕ) :
    YModule ρ m →ₗ[R] YModule ρ (m+1) := (data g ρ hg hr m).map

theorem closedMap_injective (hg : g*g=1) (hr : (1+g)*ρ=0) (m : ℕ) :
    Function.Injective (closedMap g ρ hg hr m) := (data g ρ hg hr m).injective

theorem closedMap_range (hg : g*g=1) (hr : (1+g)*ρ=0) (m : ℕ) (x : YModule ρ (m+1)) :
    x ∈ LinearMap.range (closedMap g ρ hg hr m) ↔ x.val ∈ firstSupport (2*(m+1)) :=
  (data g ρ hg hr m).range_iff x

theorem closedMap_differential (hg : g*g=1) (hr : (1+g)*ρ=0) (m : ℕ) :
    (yDifferential g ρ (m+1)).comp (closedMap g ρ hg hr m)=
      (closedMap g ρ hg hr m).comp (yDifferential g ρ m) := (data g ρ hg hr m).intertwining

noncomputable def closedEquiv (hg : g*g=1) (hr : (1+g)*ρ=0) (m : ℕ) :
    YModule ρ m ≃ₗ[R] LinearMap.range (closedMap g ρ hg hr m) :=
  LinearEquiv.ofInjective _ (closedMap_injective g ρ hg hr m)

#print axioms data
#print axioms closedMap
#print axioms closedMap_injective
#print axioms closedMap_range
#print axioms closedMap_differential
#print axioms closedEquiv

end Verification.PathClosedY
