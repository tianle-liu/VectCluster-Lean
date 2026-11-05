/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathFirstDegreeCoordinates
import Verification.DegreeMatrixCutout

/-!
# Path First Degree Boundary

Literal first differentials of the rho-zero path chain complexes, expressed
in the exhaustive empty/singleton word bases.
-/

namespace Verification.PathFirstDegreeBoundary

open Classical Verification.PathFirstDegreeCoordinates Verification.PathFirstBoundaryCutout
  Verification.PathEndpointWords Verification.PathNormalizedBasis Verification.PathStratumGrading
  Verification.PathEndpointCoordinates Verification.GradedPerturbation Verification.PathFullComplex

variable {R : Type*} [CommRing R]

noncomputable def zFirstMap (g : R) (n : ℕ) :
    degreeModule (R := R) (fun x : NormalIndex RightNormal n => -degree x) (-1) →ₗ[R]
      degreeModule (R := R) (fun x : NormalIndex RightNormal n => -degree x) 0 :=
  matrixDegreeMap _ (zMatrix g 0 n).transpose 1
    (transpose_degree _ _ (zMatrix_degree g 0 n)) (-1) 0 (by omega)

noncomputable def yFirstMap (g : R) (m : ℕ) :
    degreeModule (R := R) (fun x : NormalIndex BothNormal (2*m) => -degree x) (-1) →ₗ[R]
      degreeModule (R := R) (fun x : NormalIndex BothNormal (2*m) => -degree x) 0 :=
  matrixDegreeMap _ (yMatrix g 0 m).transpose 1
    (transpose_degree _ _ (yMatrix_degree g 0 m)) (-1) 0 (by omega)

theorem z_first_coordinates (g : R) (n : ℕ) :
    (zZeroCoordinates n).toLinearMap.comp
      ((zFirstMap g n).comp (firstCoordinates RightNormal n).symm.toLinearMap)=zBoundary g n := by
  unfold zZeroCoordinates zFirstMap firstCoordinates
  exact Verification.DegreeMatrixCutout.coordinate_cutout _ _ _ _ _ _ _ _ _

theorem y_first_coordinates (g : R) (m : ℕ) :
    (yZeroCoordinates m).toLinearMap.comp
      ((yFirstMap g m).comp (firstCoordinates BothNormal (2*m)).symm.toLinearMap)=yBoundary g m := by
  unfold yZeroCoordinates yFirstMap firstCoordinates
  exact Verification.DegreeMatrixCutout.coordinate_cutout _ _ _ _ _ _ _ _ _

#print axioms zFirstMap
#print axioms yFirstMap
#print axioms z_first_coordinates
#print axioms y_first_coordinates

end Verification.PathFirstDegreeBoundary
