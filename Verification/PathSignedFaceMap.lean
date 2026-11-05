/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathSignedFaceUnits

/-!
# Path Signed Face Map

The actual algebra map between canonical signed path coefficient charts,
with the inserted normal freely invertible. This retains all generators and
the original normal-frame sign, rather than postulating a matrix comparison.
-/
noncomputable section
namespace Verification.PathSignedFaceMap
open Verification.PathCompression Verification.PathClassRepresentatives
open Verification.PathSignedStratumCoefficients Verification.PathSignedFaceUnits
open Verification.OriginalTorus Verification.FinsuppTorusUniversal
open Verification.LaurentPolynomialUniversal
open Finset
variable (R : Type) [CommRing R] {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)
variable (a b : R) (j : ℕ) (hj : j ∈ Icc 1 n) (ha : Addable I j)

def torusMap : Torus R (Representatives n I) →ₐ[R] FaceLaurent R hI a b j hj ha :=
  FinsuppTorusUniversal.lift R _ (fun p => faceUnit R hI a b j hj ha (includeRepresentative p))

theorem torusMap_coordinate (p : Vertices n I) :
    torusMap R hI a b j hj ha (torusCoordinate R _ (compress hI p))=
      (faceUnit R hI a b j hj ha p : FaceLaurent R hI a b j hj ha) := by
  rw [torusMap,lift_coordinate]
  exact congrArg Units.val (faceUnit_compression R hI a b j hj ha p)

def coefficientMap : Coefficients R hI a b →ₐ[R] FaceLaurent R hI a b j hj ha :=
  Ideal.Quotient.liftₐ (endpointIdeal R hI a b) (torusMap R hI a b j hj ha) (by
    change endpointIdeal R hI a b ≤ RingHom.ker (torusMap R hI a b j hj ha).toRingHom
    apply Ideal.span_le.mpr
    rintro _ ⟨e,rfl⟩
    change torusMap R hI a b j hj ha (_-_)=0
    rw [map_sub,torusMap_coordinate,faceUnit_endpoint,AlgHom.commutes,sub_self])

theorem map_signed (p : Vertices n I) :
    coefficientMap R hI a b j hj ha (signedCoordinate R hI a b p : Coefficients R hI a b)=
      (faceUnit R hI a b j hj ha p : FaceLaurent R hI a b j hj ha) :=
  torusMap_coordinate R hI a b j hj ha p

theorem map_normal : coefficientMap R hI a b j hj ha
    (signedCoordinate R hI a b (normalVertex j hj ha) : Coefficients R hI a b)=
      parameter (NextCoefficients R hI a b j hj ha) := by
  rw [map_signed,faceUnit_normal,parameterUnit_val]

theorem map_remaining (p : Vertices n I) (hp : p.val≠j) :
    coefficientMap R hI a b j hj ha (signedCoordinate R hI a b p : Coefficients R hI a b)=
      algebraMap (NextCoefficients R hI a b j hj ha) _
        (signedCoordinate R (nextAdmissible hI j hj ha) a b (remainingVertex j p hp) : NextCoefficients R hI a b j hj ha) := by
  rw [map_signed,faceUnit,dif_neg hp]
  rfl

theorem map_original_normal : coefficientMap R hI a b j hj ha
    (unsignedCoordinate R hI a b (normalVertex j hj ha) : Coefficients R hI a b)=
      (-1)^(j/2)*parameter (NextCoefficients R hI a b j hj ha) := by
  change coefficientMap R hI a b j hj ha ((-1:Coefficients R hI a b)^(j/2)*
    (signedCoordinate R hI a b (normalVertex j hj ha) : Coefficients R hI a b))=_
  rw [map_mul,map_pow,map_neg,map_one,map_normal]

theorem map_original_remaining (p : Vertices n I) (hp : p.val≠j) :
    coefficientMap R hI a b j hj ha (unsignedCoordinate R hI a b p : Coefficients R hI a b)=
      algebraMap (NextCoefficients R hI a b j hj ha) _
        (unsignedCoordinate R (nextAdmissible hI j hj ha) a b (remainingVertex j p hp) : NextCoefficients R hI a b j hj ha) := by
  change coefficientMap R hI a b j hj ha ((-1:Coefficients R hI a b)^(p.val/2)*
    (signedCoordinate R hI a b p : Coefficients R hI a b))=
      algebraMap (NextCoefficients R hI a b j hj ha) _ ((-1:NextCoefficients R hI a b j hj ha)^(p.val/2)*_)
  rw [map_mul,map_pow,map_neg,map_one,map_remaining,map_mul,map_pow,map_neg,map_one]

#print axioms torusMap
#print axioms torusMap_coordinate
#print axioms coefficientMap
#print axioms map_signed
#print axioms map_normal
#print axioms map_remaining
#print axioms map_original_normal
#print axioms map_original_remaining
end Verification.PathSignedFaceMap
