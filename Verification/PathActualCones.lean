/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathActualOpenSections
import Verification.PathRecursionExactness
import Verification.PathSplitConeData

/-!
# Path Actual Cones

Literal full-rho Z and Y differentials in recursively split coordinates.
These are cochain-module block identities; degree shifts and their chain duals
are not silently identified by this construction.
-/

namespace Verification.PathActualCones

open Verification.PathEndpointComplex Verification.PathRecursionExactness
  Verification.PathActualOpenSections

variable {R : Type*} [CommRing R] (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)

noncomputable def zData (n : ℕ) :
    Verification.PathSplitConeData.ConeData (R := R) (C := ZModule ρ n)
      (M := ZModule ρ (n+2)) (O := Bool → ZModule ρ (n+1))
      (zDifferential g ρ (n+2)) (zDifferential g ρ n) (Verification.PathOpenZ.torusDifferential g ρ (n+1)) :=
  Verification.PathSplitConeData.ofSplit (R := R)
    (C := ZModule ρ n) (M := ZModule ρ (n+2)) (O := Bool → ZModule ρ (n+1))
    (Verification.PathClosedZ.closedMap g ρ hg hr n) (Verification.PathOpenZ.openMap g ρ hg hr (n+1))
    (zSection g ρ hg hr (n+1)) (Verification.PathClosedZ.closedMap_injective g ρ hg hr n)
    (z_exact g ρ hg hr n) (z_section g ρ hg hr (n+1))
    (zDifferential g ρ (n+2)) (zDifferential g ρ n) (Verification.PathOpenZ.torusDifferential g ρ (n+1))
    (Verification.PathClosedZ.closedMap_differential g ρ hg hr n)
    (Verification.PathOpenZ.openMap_differential g ρ hg hr (n+1))

noncomputable def zCoordinates (n : ℕ) : ZModule ρ (n+2) ≃ₗ[R] ZModule ρ n × (Bool → ZModule ρ (n+1)) :=
  (zData g ρ hg hr n).coordinates

noncomputable def zConnecting (n : ℕ) : (Bool → ZModule ρ (n+1)) →ₗ[R] ZModule ρ n :=
  (zData g ρ hg hr n).connecting

noncomputable def zBlock (n : ℕ) :
    (ZModule ρ n × (Bool → ZModule ρ (n+1))) →ₗ[R] (ZModule ρ n × (Bool → ZModule ρ (n+1))) :=
  Verification.PathSplitConeData.block (R := R) (C := ZModule ρ n) (O := Bool → ZModule ρ (n+1))
    (zDifferential g ρ n)
    (Verification.PathOpenZ.torusDifferential g ρ (n+1)) (zConnecting g ρ hg hr n)

theorem z_conjugacy (n : ℕ) :
    (zCoordinates g ρ hg hr n).toLinearMap.comp (zDifferential g ρ (n+2))=
      (zBlock g ρ hg hr n).comp (zCoordinates g ρ hg hr n).toLinearMap :=
  (zData g ρ hg hr n).conjugacy

noncomputable def yData (m : ℕ) :
    Verification.PathSplitConeData.ConeData (R := R) (C := YModule ρ m)
      (M := YModule ρ (m+1)) (O := ZModule ρ (2*m+1))
      (yDifferential g ρ (m+1)) (yDifferential g ρ m) (zDifferential g ρ (2*m+1)) :=
  Verification.PathSplitConeData.ofSplit (R := R)
    (C := YModule ρ m) (M := YModule ρ (m+1)) (O := ZModule ρ (2*m+1))
    (Verification.PathClosedY.closedMap g ρ hg hr m) (Verification.PathOpenY.openMap g ρ hg hr m)
    (ySection g ρ hg hr m) (Verification.PathClosedY.closedMap_injective g ρ hg hr m)
    (y_exact g ρ hg hr m) (y_section g ρ hg hr m)
    (yDifferential g ρ (m+1)) (yDifferential g ρ m) (zDifferential g ρ (2*m+1))
    (Verification.PathClosedY.closedMap_differential g ρ hg hr m)
    (Verification.PathOpenY.openMap_differential g ρ hg hr m)

noncomputable def yCoordinates (m : ℕ) : YModule ρ (m+1) ≃ₗ[R] YModule ρ m × ZModule ρ (2*m+1) :=
  (yData g ρ hg hr m).coordinates

noncomputable def yConnecting (m : ℕ) : ZModule ρ (2*m+1) →ₗ[R] YModule ρ m :=
  (yData g ρ hg hr m).connecting

noncomputable def yBlock (m : ℕ) : (YModule ρ m × ZModule ρ (2*m+1)) →ₗ[R] (YModule ρ m × ZModule ρ (2*m+1)) :=
  Verification.PathSplitConeData.block (R := R) (C := YModule ρ m) (O := ZModule ρ (2*m+1))
    (yDifferential g ρ m) (zDifferential g ρ (2*m+1)) (yConnecting g ρ hg hr m)

theorem y_conjugacy (m : ℕ) :
    (yCoordinates g ρ hg hr m).toLinearMap.comp (yDifferential g ρ (m+1))=
      (yBlock g ρ hg hr m).comp (yCoordinates g ρ hg hr m).toLinearMap :=
  (yData g ρ hg hr m).conjugacy

#print axioms zData
#print axioms zCoordinates
#print axioms zConnecting
#print axioms zBlock
#print axioms z_conjugacy
#print axioms yData
#print axioms yCoordinates
#print axioms yConnecting
#print axioms yBlock
#print axioms y_conjugacy

end Verification.PathActualCones
