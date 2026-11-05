/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathClosedDataTransport

/-!
# Path Closed Z

Actual Z closed recursion with its manuscript endpoint constants.
-/

namespace Verification.PathClosedZ

open Classical Verification.PathEndpointComplex Verification.PathEndpointRecursionConstants
  Verification.PathEndpointClosedData
  Verification.PathClosedDataTransport

variable {R : Type*} [CommRing R] (g ρ : R)

noncomputable def data (hg : g*g=1) (hr : (1+g)*ρ=0) (n : ℕ) :
    ClosedData (R := R) (M := ZModule ρ n) (N := ZModule ρ (n+2))
      (zDifferential g ρ n) (zDifferential g ρ (n+2))
      (rightSupport (endpointConstant ρ (n+2)) (n+2)) :=
  rightSource g ρ hg hr true true (endpointConstant ρ n) (endpointConstant ρ (n+2)) n
    (endpointConstant_relation ρ (n+2)) (z_source_constant g ρ hr n)

noncomputable def closedMap (hg : g*g=1) (hr : (1+g)*ρ=0) (n : ℕ) :
    ZModule ρ n →ₗ[R] ZModule ρ (n+2) := (data g ρ hg hr n).map

theorem closedMap_injective (hg : g*g=1) (hr : (1+g)*ρ=0) (n : ℕ) :
    Function.Injective (closedMap g ρ hg hr n) := (data g ρ hg hr n).injective

theorem closedMap_range (hg : g*g=1) (hr : (1+g)*ρ=0) (n : ℕ) (x : ZModule ρ (n+2)) :
    x ∈ LinearMap.range (closedMap g ρ hg hr n) ↔ x.val ∈ firstSupport (n+2) :=
  (data g ρ hg hr n).range_iff x

theorem closedMap_differential (hg : g*g=1) (hr : (1+g)*ρ=0) (n : ℕ) :
    (zDifferential g ρ (n+2)).comp (closedMap g ρ hg hr n)=
      (closedMap g ρ hg hr n).comp (zDifferential g ρ n) := (data g ρ hg hr n).intertwining

noncomputable def closedEquiv (hg : g*g=1) (hr : (1+g)*ρ=0) (n : ℕ) :
    ZModule ρ n ≃ₗ[R] LinearMap.range (closedMap g ρ hg hr n) :=
  LinearEquiv.ofInjective _ (closedMap_injective g ρ hg hr n)

#print axioms data
#print axioms closedMap
#print axioms closedMap_injective
#print axioms closedMap_range
#print axioms closedMap_differential
#print axioms closedEquiv

end Verification.PathClosedZ
