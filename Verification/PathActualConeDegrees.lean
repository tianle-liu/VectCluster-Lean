/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathActualConeCoordinates
import Verification.PathActualRecursionDegree
import Verification.PathClosedReflectionTransport
import Verification.PathDifferentialDegree

/-!
# Path Actual Cone Degrees

The complete recursive cone coordinates, in both directions, carry the
actual cellular grading. Their connecting operators have degree zero on
the shorter models; the closed summand itself has the degree-one shift.
-/

namespace Verification.PathActualConeDegrees

open Verification.PathEndpointComplex Verification.PathActualCones
  Verification.PathActualConeCoordinates Verification.PathActualRecursionDegree
  Verification.PathClosedReflectionTransport Verification.PathDifferentialDegree
  Verification.PathRecursionDegree Verification.PathProjectedDegree

variable {R : Type*} [CommRing R] (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)

theorem z_coordinates_degree (n : ℕ) (p : ℤ) (x : ZModule ρ (n+2))
    (hx : TotalDegree (n+2) p x.val) :
    TotalDegree n (p-1) (zCoordinates g ρ hg hr n x).1.val ∧
      ∀ bit, TotalDegree (n+1) p ((zCoordinates g ρ hg hr n x).2 bit).val := by
  have ho := z_open_degree g ρ hg hr (n+1) p x hx
  constructor
  · apply z_closed_reflects g ρ hg hr n (p-1)
    rw [z_first_image,sub_add_cancel]
    exact degree_sub hx (z_section_degree g ρ hg hr (n+1) p _ ho)
  · rw [z_second]
    exact ho

theorem y_coordinates_degree (m : ℕ) (p : ℤ) (x : YModule ρ (m+1))
    (hx : TotalDegree (2*(m+1)) p x.val) :
    TotalDegree (2*m) (p-1) (yCoordinates g ρ hg hr m x).1.val ∧
      TotalDegree (2*m+1) p (yCoordinates g ρ hg hr m x).2.val := by
  have ho := y_open_degree g ρ hg hr m p x hx
  constructor
  · apply y_closed_reflects g ρ hg hr m (p-1)
    rw [y_first_image,sub_add_cancel]
    exact degree_sub hx (y_section_degree g ρ hg hr m p _ ho)
  · rw [y_second]
    exact ho

theorem z_inverse_degree (n : ℕ) (p : ℤ) (x : ZModule ρ n × (Bool → ZModule ρ (n+1)))
    (hc : TotalDegree n (p-1) x.1.val) (ho : ∀ bit, TotalDegree (n+1) p (x.2 bit).val) :
    TotalDegree (n+2) p ((zCoordinates g ρ hg hr n).symm x).val := by
  rw [z_inverse]
  apply degree_add
  · simpa only [sub_add_cancel] using z_closed_degree g ρ hg hr n (p-1) x.1 hc
  · exact z_section_degree g ρ hg hr (n+1) p x.2 ho

theorem y_inverse_degree (m : ℕ) (p : ℤ) (x : YModule ρ m × ZModule ρ (2*m+1))
    (hc : TotalDegree (2*m) (p-1) x.1.val) (ho : TotalDegree (2*m+1) p x.2.val) :
    TotalDegree (2*(m+1)) p ((yCoordinates g ρ hg hr m).symm x).val := by
  rw [y_inverse]
  apply degree_add
  · simpa only [sub_add_cancel] using y_closed_degree g ρ hg hr m (p-1) x.1 hc
  · exact y_section_degree g ρ hg hr m p x.2 ho

theorem z_connecting_degree (n : ℕ) (p : ℤ) (x : Bool → ZModule ρ (n+1))
    (hx : ∀ bit, TotalDegree (n+1) p (x bit).val) :
    TotalDegree n p (zConnecting g ρ hg hr n x).val := by
  rw [z_connecting]
  have hh := (z_coordinates_degree g ρ hg hr n (p+1) _
    (z_differential_degree g ρ (n+2) p _ (z_section_degree g ρ hg hr (n+1) p x hx))).1
  simpa only [add_sub_cancel_right] using hh

theorem y_connecting_degree (m : ℕ) (p : ℤ) (x : ZModule ρ (2*m+1))
    (hx : TotalDegree (2*m+1) p x.val) :
    TotalDegree (2*m) p (yConnecting g ρ hg hr m x).val := by
  rw [y_connecting]
  have hh := (y_coordinates_degree g ρ hg hr m (p+1) _
    (y_differential_degree g ρ (m+1) p _ (y_section_degree g ρ hg hr m p x hx))).1
  simpa only [add_sub_cancel_right] using hh

#print axioms z_coordinates_degree
#print axioms y_coordinates_degree
#print axioms z_inverse_degree
#print axioms y_inverse_degree
#print axioms z_connecting_degree
#print axioms y_connecting_degree

end Verification.PathActualConeDegrees
