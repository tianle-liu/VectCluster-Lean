/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathSignedFaceMap
import Verification.LaurentSignChange

/-!
# Path Face Vertex Transport

Actual unit images of a signed compressed face: the two new neighbors
are one target unit and the normal is the signed Laurent parameter.
-/
noncomputable section
namespace Verification.PathFaceVertexTransport
open Verification.PathCompression Verification.PathClassRepresentatives
open Verification.PathSignedStratumCoefficients Verification.PathSignedFaceUnits
open Verification.PathLiteralStratum Verification.LaurentPolynomialUniversal Finset
variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
variable {n : ℕ} {I : Finset ℕ} (hI : Admissible n I) (a b : S)
variable (j : ℕ) (hj : j∈Icc 1 n) (ha : Addable I j) (w : ℕ)
local notation "hJ" => nextAdmissible hI j hj ha
local notation "Cnew" => Coefficients S (nextAdmissible hI j hj ha) a b

def oldVertex (p : Vertices n (insert j I)) : Vertices n I :=
  ⟨p.val,mem_sdiff.mpr ⟨(mem_sdiff.mp p.property).1,
    fun hp => (mem_sdiff.mp p.property).2 (mem_insert_of_mem hp)⟩⟩

def map : Coefficients S hI a b →ₐ[R] Laurent Cnew :=
  (LaurentSignChange.map R Cnew w).comp
    ((PathSignedFaceMap.coefficientMap S hI a b j hj ha).restrictScalars R)

theorem remaining (p : Vertices n (insert j I)) :
    map R S hI a b j hj ha w (signedCoordinate S hI a b (oldVertex j p) : Coefficients S hI a b)=
      algebraMap Cnew (Laurent Cnew) (signedCoordinate S hJ a b p : Cnew) := by
  have hp : (oldVertex j p).val≠j := by
    intro he
    exact (mem_sdiff.mp p.property).2 (mem_insert.mpr (Or.inl he))
  change LaurentSignChange.map R Cnew w
    (PathSignedFaceMap.coefficientMap S hI a b j hj ha _)=_
  rw [PathSignedFaceMap.map_remaining S hI a b j hj ha (oldVertex j p) hp,LaurentSignChange.coefficient]
  congr 2

theorem normal : map R S hI a b j hj ha w
    (signedCoordinate S hI a b (normalVertex j hj ha) : Coefficients S hI a b)=
      (-1)^w*parameter Cnew := by
  change LaurentSignChange.map R Cnew w
    (PathSignedFaceMap.coefficientMap S hI a b j hj ha _)=_
  rw [PathSignedFaceMap.map_normal,LaurentSignChange.parameter]

theorem neighbors : signedCoordinate S hJ a b (rightVertex hJ ⟨j,mem_insert_self j I⟩)=
    signedCoordinate S hJ a b (leftVertex hJ ⟨j,mem_insert_self j I⟩) := by
  unfold signedCoordinate
  rw [compress_neighbors]


theorem remaining_unit (p : Vertices n (insert j I)) :
    Units.map (map R S hI a b j hj ha w).toRingHom.toMonoidHom
      (signedCoordinate S hI a b (oldVertex j p))=
    Units.map (algebraMap Cnew (Laurent Cnew)).toMonoidHom (signedCoordinate S hJ a b p) :=
  Units.ext (remaining R S hI a b j hj ha w p)

theorem normal_unit : Units.map (map R S hI a b j hj ha w).toRingHom.toMonoidHom
    (signedCoordinate S hI a b (normalVertex j hj ha))=(-1)^w*parameterUnit Cnew := by
  apply Units.ext
  change map R S hI a b j hj ha w (signedCoordinate S hI a b (normalVertex j hj ha) : Coefficients S hI a b)=_
  rw [normal,Units.val_mul,Units.val_pow_eq_pow_val,Units.val_neg,Units.val_one,parameterUnit_val]

#print axioms oldVertex
#print axioms map
#print axioms remaining
#print axioms normal
#print axioms neighbors
#print axioms remaining_unit
#print axioms normal_unit
end Verification.PathFaceVertexTransport
