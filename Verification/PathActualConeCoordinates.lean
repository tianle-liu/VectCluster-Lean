/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathActualCones

/-!
# Path Actual Cone Coordinates

Coordinate formulas for the literal split Z/Y cones. In particular the
closed coordinate is recovered from the original vector minus its chosen
open lift, so it is available for degree and weight support proofs.
-/

namespace Verification.PathActualConeCoordinates

open Verification.PathEndpointComplex Verification.PathActualCones
  Verification.PathActualOpenSections Verification.PathRecursionExactness

variable {R : Type*} [CommRing R] (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)

theorem z_first_image (n : ℕ) (x : ZModule ρ (n+2)) :
    Verification.PathClosedZ.closedMap g ρ hg hr n (zCoordinates g ρ hg hr n x).1=
      x-zSection g ρ hg hr (n+1) (Verification.PathOpenZ.openMap g ρ hg hr (n+1) x) :=
  Verification.PathSplitRecursion.closedRetraction_image (R := R)
    (C := ZModule ρ n) (M := ZModule ρ (n+2)) (O := Bool → ZModule ρ (n+1))
    (Verification.PathClosedZ.closedMap g ρ hg hr n) (Verification.PathOpenZ.openMap g ρ hg hr (n+1))
    (zSection g ρ hg hr (n+1)) (Verification.PathClosedZ.closedMap_injective g ρ hg hr n)
    (z_exact g ρ hg hr n) (z_section g ρ hg hr (n+1)) x

theorem z_second (n : ℕ) (x : ZModule ρ (n+2)) :
    (zCoordinates g ρ hg hr n x).2=Verification.PathOpenZ.openMap g ρ hg hr (n+1) x := rfl

theorem z_inverse (n : ℕ) (x : ZModule ρ n × (Bool → ZModule ρ (n+1))) :
    (zCoordinates g ρ hg hr n).symm x=
      Verification.PathClosedZ.closedMap g ρ hg hr n x.1+zSection g ρ hg hr (n+1) x.2 := rfl

theorem z_connecting (n : ℕ) (x : Bool → ZModule ρ (n+1)) :
    zConnecting g ρ hg hr n x=
      (zCoordinates g ρ hg hr n (zDifferential g ρ (n+2) (zSection g ρ hg hr (n+1) x))).1 := rfl

theorem y_first_image (m : ℕ) (x : YModule ρ (m+1)) :
    Verification.PathClosedY.closedMap g ρ hg hr m (yCoordinates g ρ hg hr m x).1=
      x-ySection g ρ hg hr m (Verification.PathOpenY.openMap g ρ hg hr m x) :=
  Verification.PathSplitRecursion.closedRetraction_image (R := R)
    (C := YModule ρ m) (M := YModule ρ (m+1)) (O := ZModule ρ (2*m+1))
    (Verification.PathClosedY.closedMap g ρ hg hr m) (Verification.PathOpenY.openMap g ρ hg hr m)
    (ySection g ρ hg hr m) (Verification.PathClosedY.closedMap_injective g ρ hg hr m)
    (y_exact g ρ hg hr m) (y_section g ρ hg hr m) x

theorem y_second (m : ℕ) (x : YModule ρ (m+1)) :
    (yCoordinates g ρ hg hr m x).2=Verification.PathOpenY.openMap g ρ hg hr m x := rfl

theorem y_inverse (m : ℕ) (x : YModule ρ m × ZModule ρ (2*m+1)) :
    (yCoordinates g ρ hg hr m).symm x=
      Verification.PathClosedY.closedMap g ρ hg hr m x.1+ySection g ρ hg hr m x.2 := rfl

theorem y_connecting (m : ℕ) (x : ZModule ρ (2*m+1)) :
    yConnecting g ρ hg hr m x=
      (yCoordinates g ρ hg hr m (yDifferential g ρ (m+1) (ySection g ρ hg hr m x))).1 := rfl

#print axioms z_first_image
#print axioms z_second
#print axioms z_inverse
#print axioms z_connecting
#print axioms y_first_image
#print axioms y_second
#print axioms y_inverse
#print axioms y_connecting

end Verification.PathActualConeCoordinates
