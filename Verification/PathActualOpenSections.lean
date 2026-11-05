/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOpenSectionTransport
import Verification.PathOpenZ
import Verification.PathOpenY

/-!
# Path Actual Open Sections

Explicit split sections for the actual manuscript Z and Y open restrictions.
-/

namespace Verification.PathActualOpenSections

open Verification.PathEndpointComplex Verification.PathOpenConstants Verification.PathOpenSectionTransport

variable {R : Type*} [CommRing R] (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)

noncomputable def zSectionData (n : ℕ) :
    {S : (Bool → ZModule ρ n) →ₗ[R] ZModule ρ (n+1) //
      (Verification.PathOpenZ.openMap g ρ hg hr n).comp S=LinearMap.id} :=
  rightTargetSection g ρ hg hr false true (endpointConstant ρ (n+1)) (endpointConstant ρ n) n
    (endpointConstant_relation ρ (n+1)) (endpoint_one_step g ρ hr n)

noncomputable def zSection (n : ℕ) : (Bool → ZModule ρ n) →ₗ[R] ZModule ρ (n+1) :=
  (zSectionData g ρ hg hr n).val

theorem z_section (n : ℕ) :
    (Verification.PathOpenZ.openMap g ρ hg hr n).comp (zSection g ρ hg hr n)=LinearMap.id :=
  (zSectionData g ρ hg hr n).property

noncomputable def ySectionData (m : ℕ) :
    {S : ZModule ρ (2*m+1) →ₗ[R] YModule ρ (m+1) //
      (Verification.PathOpenY.openMap g ρ hg hr m).comp S=LinearMap.id} :=
  bothTargetSectionSize g ρ hg hr false true (endpointConstant ρ (2*(m+1)))
    (endpointConstant ρ (2*m+1)) (2*m+1) (2*(m+1)) (by omega)
    (endpointConstant_relation ρ (2*(m+1)))
    (by simpa only [Nat.mul_add,Nat.mul_one,Nat.add_assoc] using endpoint_one_step g ρ hr (2*m+1))

noncomputable def ySection (m : ℕ) : ZModule ρ (2*m+1) →ₗ[R] YModule ρ (m+1) :=
  (ySectionData g ρ hg hr m).val

theorem y_section (m : ℕ) :
    (Verification.PathOpenY.openMap g ρ hg hr m).comp (ySection g ρ hg hr m)=LinearMap.id :=
  (ySectionData g ρ hg hr m).property

#print axioms zSectionData
#print axioms zSection
#print axioms z_section
#print axioms ySectionData
#print axioms ySection
#print axioms y_section

end Verification.PathActualOpenSections
