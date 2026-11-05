/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.BoolMatrixCopies
import Verification.PathActualConeMatrices

/-!
# Path Torus Matrix

The original Z open-layer matrix in its actual Bool sigma coordinates is
exactly two copies of the shorter path matrix, including all rho terms.
-/

namespace Verification.PathTorusMatrix

open Verification.PathActualConeMatrices Verification.PathEndpointCoordinates
  Verification.PathEndpointComplex Verification.PathConeCoefficients

variable {R : Type} [CommRing R]

theorem mulVec (g ρ : R) (n : ℕ) (x : TorusIndex n → R) (b : Bool)
    (i : Verification.PathNormalizedBasis.NormalIndex Verification.PathEndpointWords.RightNormal n) :
    (torusMatrix g ρ n).mulVec x ⟨b,i⟩=(zMatrix g ρ n).mulVec (fun j => x ⟨b,j⟩) i := by
  rw [torusMatrix,matrixOf_mulVec (R := R) (C := Bool → ZModule ρ n)
    (torusCoefficients ρ n) (Verification.PathOpenZ.torusDifferential g ρ n) x]
  change (zCoefficients ρ n (zDifferential g ρ n ((zCoefficients ρ n).symm (fun j => x ⟨b,j⟩)))) i=_
  exact (congrFun (matrixOf_mulVec (R := R) (C := ZModule ρ n)
    (zCoefficients ρ n) (zDifferential g ρ n) (fun j => x ⟨b,j⟩)) i).symm

theorem matrix_eq (g ρ : R) (n : ℕ) :
    torusMatrix g ρ n=Verification.BoolMatrixCopies.copy (zMatrix g ρ n) := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  funext i
  change (torusMatrix g ρ n).mulVec x i=(Verification.BoolMatrixCopies.copy (zMatrix g ρ n)).mulVec x i
  rw [mulVec,Verification.BoolMatrixCopies.mulVec_apply]

theorem transpose_eq (g ρ : R) (n : ℕ) :
    (torusMatrix g ρ n).transpose=Verification.BoolMatrixCopies.copy (zMatrix g ρ n).transpose := by
  rw [matrix_eq,Verification.BoolMatrixCopies.copy,Matrix.blockDiagonal'_transpose]
  rfl

#print axioms mulVec
#print axioms matrix_eq
#print axioms transpose_eq

end Verification.PathTorusMatrix
