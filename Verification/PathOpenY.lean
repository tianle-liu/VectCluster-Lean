/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOpenDataTransport
import Verification.PathOpenConstants

/-!
# Path Open Y

Actual Y open recursion onto the shorter Z module, with full rho terms.
-/

namespace Verification.PathOpenY

open Verification.PathEndpointComplex Verification.PathEndpointClosedData
  Verification.PathOpenData Verification.PathOpenDataTransport Verification.PathOpenConstants

variable {R : Type*} [CommRing R] (g ρ : R)

noncomputable def data (hg : g*g=1) (hr : (1+g)*ρ=0) (m : ℕ) :
    OpenData (R := R) (M := YModule ρ (m+1)) (N := ZModule ρ (2*m+1))
      (yDifferential g ρ (m+1)) (zDifferential g ρ (2*m+1))
      (bothSupport 0 (endpointConstant ρ (2*(m+1))) (2*(m+1))) :=
  bothTargetSize g ρ hg hr false true (endpointConstant ρ (2*(m+1)))
    (endpointConstant ρ (2*m+1)) (2*m+1) (2*(m+1)) (by omega)
    (endpointConstant_relation ρ (2*(m+1)))
    (by simpa only [Nat.mul_add,Nat.mul_one,Nat.add_assoc] using endpoint_one_step g ρ hr (2*m+1))

noncomputable def openMap (hg : g*g=1) (hr : (1+g)*ρ=0) (m : ℕ) :
    YModule ρ (m+1) →ₗ[R] ZModule ρ (2*m+1) := (data g ρ hg hr m).map

theorem openMap_surjective (hg : g*g=1) (hr : (1+g)*ρ=0) (m : ℕ) :
    Function.Surjective (openMap g ρ hg hr m) := (data g ρ hg hr m).surjective

theorem openMap_kernel (hg : g*g=1) (hr : (1+g)*ρ=0) (m : ℕ) (x : YModule ρ (m+1)) :
    openMap g ρ hg hr m x=0 ↔ x.val ∈ firstSupport (2*(m+1)) := (data g ρ hg hr m).kernel_iff x

theorem openMap_differential (hg : g*g=1) (hr : (1+g)*ρ=0) (m : ℕ) :
    (openMap g ρ hg hr m).comp (yDifferential g ρ (m+1))=
      (zDifferential g ρ (2*m+1)).comp (openMap g ρ hg hr m) := (data g ρ hg hr m).intertwining

#print axioms data
#print axioms openMap
#print axioms openMap_surjective
#print axioms openMap_kernel
#print axioms openMap_differential

end Verification.PathOpenY
