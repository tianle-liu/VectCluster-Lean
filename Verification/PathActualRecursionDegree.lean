/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathDegreeTransport

/-!
# Path Actual Recursion Degree

The actual manuscript Z/Y endpoint recursions have their asserted degrees.
-/

namespace Verification.PathActualRecursionDegree

open Verification.PathEndpointComplex Verification.PathEndpointRecursionConstants
  Verification.PathOpenConstants Verification.PathRecursionDegree Verification.PathDegreeTransport

variable {R : Type*} [CommRing R] (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)

theorem z_closed_degree (n : ℕ) (p : ℤ) (x : ZModule ρ n) (hx : TotalDegree n p x.val) :
    TotalDegree (n+2) (p+1) (Verification.PathClosedZ.closedMap g ρ hg hr n x).val :=
  rightSource_degree g ρ hg hr true true (endpointConstant ρ n) (endpointConstant ρ (n+2)) n
    (endpointConstant_relation ρ (n+2)) (z_source_constant g ρ hr n) p x hx

theorem y_closed_degree (m : ℕ) (p : ℤ) (x : YModule ρ m) (hx : TotalDegree (2*m) p x.val) :
    TotalDegree (2*(m+1)) (p+1) (Verification.PathClosedY.closedMap g ρ hg hr m x).val :=
  bothSourceSize_degree g ρ hg hr false true 0 (endpointConstant ρ (2*m)) 0
    (endpointConstant ρ (2*(m+1))) m (2*(m+1)) (by omega)
    (by simp) (by simp) (endpointConstant_relation ρ (2*(m+1))) rfl
      (by simpa only [Nat.mul_add,Nat.mul_one] using y_source_right_constant g ρ hr m) p x hx

theorem z_open_degree (n : ℕ) (p : ℤ) (x : ZModule ρ (n+1)) (hx : TotalDegree (n+1) p x.val)
    (bit : Bool) : TotalDegree n p (Verification.PathOpenZ.openMap g ρ hg hr n x bit).val :=
  rightTarget_degree g ρ hg hr false true (endpointConstant ρ (n+1)) (endpointConstant ρ n) n
    (endpointConstant_relation ρ (n+1)) (endpoint_one_step g ρ hr n) p x hx bit

theorem y_open_degree (m : ℕ) (p : ℤ) (x : YModule ρ (m+1)) (hx : TotalDegree (2*(m+1)) p x.val) :
    TotalDegree (2*m+1) p (Verification.PathOpenY.openMap g ρ hg hr m x).val :=
  bothTargetSize_degree g ρ hg hr false true (endpointConstant ρ (2*(m+1)))
    (endpointConstant ρ (2*m+1)) (2*m+1) (2*(m+1)) (by omega)
    (endpointConstant_relation ρ (2*(m+1)))
    (by simpa only [Nat.mul_add,Nat.mul_one,Nat.add_assoc] using endpoint_one_step g ρ hr (2*m+1)) p x hx

theorem z_section_degree (n : ℕ) (p : ℤ) (x : Bool → ZModule ρ n)
    (hx : ∀ bit, TotalDegree n p (x bit).val) :
    TotalDegree (n+1) p (Verification.PathActualOpenSections.zSection g ρ hg hr n x).val :=
  rightTargetSection_degree g ρ hg hr false true (endpointConstant ρ (n+1)) (endpointConstant ρ n) n
    (endpointConstant_relation ρ (n+1)) (endpoint_one_step g ρ hr n) p x hx

theorem y_section_degree (m : ℕ) (p : ℤ) (x : ZModule ρ (2*m+1)) (hx : TotalDegree (2*m+1) p x.val) :
    TotalDegree (2*(m+1)) p (Verification.PathActualOpenSections.ySection g ρ hg hr m x).val :=
  bothTargetSectionSize_degree g ρ hg hr false true (endpointConstant ρ (2*(m+1)))
    (endpointConstant ρ (2*m+1)) (2*m+1) (2*(m+1)) (by omega)
    (endpointConstant_relation ρ (2*(m+1)))
    (by simpa only [Nat.mul_add,Nat.mul_one,Nat.add_assoc] using endpoint_one_step g ρ hr (2*m+1)) p x hx

#print axioms z_closed_degree
#print axioms y_closed_degree
#print axioms z_open_degree
#print axioms y_open_degree
#print axioms z_section_degree
#print axioms y_section_degree

end Verification.PathActualRecursionDegree
