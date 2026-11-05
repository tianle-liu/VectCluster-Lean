/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathActualCones
import Verification.PathConeMatrixData

/-!
# Path Actual Cone Matrices

Literal finite block matrices of the actual Z/Y recursive cones.
The off-diagonal entries are evaluated from the already constructed full
rho connecting maps; no matrix conjugacy is assumed.
-/

namespace Verification.PathActualConeMatrices

open Verification.PathEndpointComplex Verification.PathEndpointWords Verification.PathNormalizedBasis
  Verification.PathEndpointCoordinates Verification.PathActualCones Verification.PathConeCoefficients

variable {R : Type*} [CommRing R]

abbrev TorusIndex (n : ℕ) := Σ _ : Bool, NormalIndex RightNormal n
abbrev ZRecursiveIndex (n : ℕ) := NormalIndex RightNormal n ⊕ TorusIndex (n+1)
abbrev YRecursiveIndex (m : ℕ) := NormalIndex BothNormal (2*m) ⊕ NormalIndex RightNormal (2*m+1)

noncomputable def torusCoefficients (ρ : R) (n : ℕ) :
    (Bool → ZModule ρ n) ≃ₗ[R] (TorusIndex n → R) :=
  (LinearEquiv.piCongrRight (fun _ : Bool => zCoefficients ρ n)).trans
    (LinearEquiv.piCurry R (fun (_ : Bool) (_ : NormalIndex RightNormal n) => R)).symm

noncomputable def torusMatrix (g ρ : R) (n : ℕ) : Matrix (TorusIndex n) (TorusIndex n) R :=
  matrixOf (M := Bool → ZModule ρ n) (torusCoefficients ρ n) (Verification.PathOpenZ.torusDifferential g ρ n)

variable (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)

noncomputable def zMatrixData (n : ℕ) :
    Verification.PathConeMatrixData.MatrixData (R := R) (M := ZModule ρ (n+2))
      (zDifferential g ρ (n+2)) (zMatrix g ρ n) (torusMatrix g ρ (n+1)) :=
  Verification.PathConeMatrixData.ofConeData (R := R) (M := ZModule ρ (n+2))
    (C := ZModule ρ n) (O := Bool → ZModule ρ (n+1))
    (zDifferential g ρ (n+2)) (zDifferential g ρ n) (Verification.PathOpenZ.torusDifferential g ρ (n+1))
    (zData g ρ hg hr n) (zCoefficients ρ n) (torusCoefficients ρ (n+1))
    (zDifferential_squared g ρ (n+2) hg hr)

noncomputable def yMatrixData (m : ℕ) :
    Verification.PathConeMatrixData.MatrixData (R := R) (M := YModule ρ (m+1))
      (yDifferential g ρ (m+1)) (yMatrix g ρ m) (zMatrix g ρ (2*m+1)) :=
  Verification.PathConeMatrixData.ofConeData (R := R) (M := YModule ρ (m+1))
    (C := YModule ρ m) (O := ZModule ρ (2*m+1))
    (yDifferential g ρ (m+1)) (yDifferential g ρ m) (zDifferential g ρ (2*m+1))
    (yData g ρ hg hr m) (yCoefficients ρ m) (zCoefficients ρ (2*m+1))
    (yDifferential_squared g ρ (m+1) hg hr)

noncomputable def zConnectingMatrix (n : ℕ) : Matrix (NormalIndex RightNormal n) (TorusIndex (n+1)) R :=
  (zMatrixData g ρ hg hr n).connecting

noncomputable def yConnectingMatrix (m : ℕ) : Matrix (NormalIndex BothNormal (2*m)) (NormalIndex RightNormal (2*m+1)) R :=
  (yMatrixData g ρ hg hr m).connecting

noncomputable def zRecursiveCoefficients (n : ℕ) : ZModule ρ (n+2) ≃ₗ[R] (ZRecursiveIndex n → R) :=
  (zMatrixData g ρ hg hr n).coordinates

noncomputable def yRecursiveCoefficients (m : ℕ) : YModule ρ (m+1) ≃ₗ[R] (YRecursiveIndex m → R) :=
  (yMatrixData g ρ hg hr m).coordinates

noncomputable def zRecursiveMatrix (n : ℕ) : Matrix (ZRecursiveIndex n) (ZRecursiveIndex n) R :=
  matrixOf (M := ZModule ρ (n+2)) (zRecursiveCoefficients g ρ hg hr n) (zDifferential g ρ (n+2))

noncomputable def yRecursiveMatrix (m : ℕ) : Matrix (YRecursiveIndex m) (YRecursiveIndex m) R :=
  matrixOf (M := YModule ρ (m+1)) (yRecursiveCoefficients g ρ hg hr m) (yDifferential g ρ (m+1))

theorem z_recursive_matrix (n : ℕ) :
    zRecursiveMatrix g ρ hg hr n=Matrix.fromBlocks (zMatrix g ρ n)
      (zConnectingMatrix g ρ hg hr n) 0 (torusMatrix g ρ (n+1)) :=
  (zMatrixData g ρ hg hr n).block_equality

theorem y_recursive_matrix (m : ℕ) :
    yRecursiveMatrix g ρ hg hr m=Matrix.fromBlocks (yMatrix g ρ m)
      (yConnectingMatrix g ρ hg hr m) 0 (zMatrix g ρ (2*m+1)) :=
  (yMatrixData g ρ hg hr m).block_equality

theorem z_recursive_square (n : ℕ) : zRecursiveMatrix g ρ hg hr n*zRecursiveMatrix g ρ hg hr n=0 :=
  (zMatrixData g ρ hg hr n).squared

theorem y_recursive_square (m : ℕ) : yRecursiveMatrix g ρ hg hr m*yRecursiveMatrix g ρ hg hr m=0 :=
  (yMatrixData g ρ hg hr m).squared

#print axioms TorusIndex
#print axioms ZRecursiveIndex
#print axioms YRecursiveIndex
#print axioms torusCoefficients
#print axioms torusMatrix
#print axioms zMatrixData
#print axioms yMatrixData
#print axioms zConnectingMatrix
#print axioms yConnectingMatrix
#print axioms zRecursiveCoefficients
#print axioms yRecursiveCoefficients
#print axioms zRecursiveMatrix
#print axioms yRecursiveMatrix
#print axioms z_recursive_matrix
#print axioms y_recursive_matrix
#print axioms z_recursive_square
#print axioms y_recursive_square

end Verification.PathActualConeMatrices
