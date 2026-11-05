/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOpenZ
import Verification.PathOpenY
import Verification.PathClosedZ
import Verification.PathClosedY

/-!
# Path Recursion Exactness

Literal exactness of the original full-rho open/closed recursions.
The maps have already been proved to intertwine the actual path differentials.
-/

namespace Verification.PathRecursionExactness

open Verification.PathEndpointComplex

variable {R : Type*} [CommRing R] (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)

theorem z_exact (n : ℕ) :
    LinearMap.range (Verification.PathClosedZ.closedMap g ρ hg hr n)=
      LinearMap.ker (Verification.PathOpenZ.openMap g ρ hg hr (n+1)) := by
  ext x
  change x ∈ LinearMap.range (Verification.PathClosedZ.closedMap g ρ hg hr n) ↔
    Verification.PathOpenZ.openMap g ρ hg hr (n+1) x=0
  rw [Verification.PathClosedZ.closedMap_range,Verification.PathOpenZ.openMap_kernel]

theorem y_exact (m : ℕ) :
    LinearMap.range (Verification.PathClosedY.closedMap g ρ hg hr m)=
      LinearMap.ker (Verification.PathOpenY.openMap g ρ hg hr m) := by
  ext x
  change x ∈ LinearMap.range (Verification.PathClosedY.closedMap g ρ hg hr m) ↔
    Verification.PathOpenY.openMap g ρ hg hr m x=0
  rw [Verification.PathClosedY.closedMap_range,Verification.PathOpenY.openMap_kernel]

theorem z_open_closed (n : ℕ) :
    (Verification.PathOpenZ.openMap g ρ hg hr (n+1)).comp
      (Verification.PathClosedZ.closedMap g ρ hg hr n)=0 := by
  apply LinearMap.ext
  intro x
  change Verification.PathClosedZ.closedMap g ρ hg hr n x ∈
    LinearMap.ker (Verification.PathOpenZ.openMap g ρ hg hr (n+1))
  rw [← z_exact g ρ hg hr n]
  exact ⟨x,rfl⟩

theorem y_open_closed (m : ℕ) :
    (Verification.PathOpenY.openMap g ρ hg hr m).comp
      (Verification.PathClosedY.closedMap g ρ hg hr m)=0 := by
  apply LinearMap.ext
  intro x
  change Verification.PathClosedY.closedMap g ρ hg hr m x ∈
    LinearMap.ker (Verification.PathOpenY.openMap g ρ hg hr m)
  rw [← y_exact g ρ hg hr m]
  exact ⟨x,rfl⟩

#print axioms z_exact
#print axioms y_exact
#print axioms z_open_closed
#print axioms y_open_closed

end Verification.PathRecursionExactness
