/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOpenDataTransport
import Verification.PathOpenConstants

/-!
# Path Open Z

Actual Z open recursion with the manuscript's endpoint constants.
-/

namespace Verification.PathOpenZ

open Verification.PathEndpointComplex Verification.PathEndpointClosedData
  Verification.PathOpenData Verification.PathOpenDataTransport Verification.PathOpenConstants

variable {R : Type*} [CommRing R] (g ρ : R)

noncomputable def torusDifferential (n : ℕ) : (Bool → ZModule ρ n) →ₗ[R] (Bool → ZModule ρ n) :=
  Verification.PathOpenRecursion.torusDifferential g ρ (endpointConstant ρ n) n

noncomputable def data (hg : g*g=1) (hr : (1+g)*ρ=0) (n : ℕ) :
    OpenData (R := R) (M := ZModule ρ (n+1)) (N := Bool → ZModule ρ n)
      (zDifferential g ρ (n+1)) (torusDifferential g ρ n)
      (rightSupport (endpointConstant ρ (n+1)) (n+1)) :=
  rightTarget g ρ hg hr false true (endpointConstant ρ (n+1)) (endpointConstant ρ n) n
    (endpointConstant_relation ρ (n+1)) (endpoint_one_step g ρ hr n)

noncomputable def openMap (hg : g*g=1) (hr : (1+g)*ρ=0) (n : ℕ) :
    ZModule ρ (n+1) →ₗ[R] (Bool → ZModule ρ n) := (data g ρ hg hr n).map

theorem openMap_surjective (hg : g*g=1) (hr : (1+g)*ρ=0) (n : ℕ) :
    Function.Surjective (openMap g ρ hg hr n) := (data g ρ hg hr n).surjective

theorem openMap_kernel (hg : g*g=1) (hr : (1+g)*ρ=0) (n : ℕ) (x : ZModule ρ (n+1)) :
    openMap g ρ hg hr n x=0 ↔ x.val ∈ firstSupport (n+1) := (data g ρ hg hr n).kernel_iff x

theorem openMap_differential (hg : g*g=1) (hr : (1+g)*ρ=0) (n : ℕ) :
    (openMap g ρ hg hr n).comp (zDifferential g ρ (n+1))=
      (torusDifferential g ρ n).comp (openMap g ρ hg hr n) := (data g ρ hg hr n).intertwining

#print axioms torusDifferential
#print axioms data
#print axioms openMap
#print axioms openMap_surjective
#print axioms openMap_kernel
#print axioms openMap_differential

end Verification.PathOpenZ
