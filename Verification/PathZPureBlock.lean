/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PureConeInductionStep
import Verification.PathRecursiveChain
import Verification.PathTorusMatrix

/-!
# Path Z Pure Block

Literal Z recursive chain blocks and their genuine degree-zero homology
basis. The degree and matrix equalities are proved from the original recursion.
-/

namespace Verification.PathZPureBlock

open Classical CategoryTheory Verification.GradedPerturbation Verification.PathEndpointWords
  Verification.PathNormalizedBasis Verification.PathStratumGrading
  Verification.PathEndpointCoordinates Verification.PathActualConeMatrices
  Verification.PathRecursiveDegreeCoefficients Verification.PathFullComplex

variable {R : Type} [CommRing R]

def degree (n : ℕ) : ZRecursiveIndex n → ℤ :=
  Verification.LowerConeRetraction.degree (fun x => -Verification.PathStratumGrading.degree x)
    (fun x => -Verification.PathStratumGrading.degree x.2)

theorem degree_eq (n : ℕ) : (fun x => -zDegree n x)=degree n := by
  funext x
  cases x with
  | inl x => change -(Verification.PathStratumGrading.degree x+1)= -Verification.PathStratumGrading.degree x-1; omega
  | inr x => rfl

noncomputable def matrix (g : R) (hg : g*g=1) (n : ℕ) : Matrix (ZRecursiveIndex n) (ZRecursiveIndex n) R :=
  Matrix.fromBlocks (zMatrix g 0 n).transpose 0 (zConnectingMatrix g 0 hg (by simp) n).transpose
    (Verification.BoolMatrixCopies.copy (zMatrix g 0 (n+1)).transpose)

theorem matrix_eq (g : R) (hg : g*g=1) (n : ℕ) :
    (zRecursiveMatrix g 0 hg (by simp) n).transpose=matrix g hg n :=
  by rw [Verification.PathRecursiveChain.z_chain_blocks,Verification.PathTorusMatrix.transpose_eq]; rfl

theorem matrix_degree (g : R) (hg : g*g=1) (n : ℕ) : Homogeneous (degree n) 1 (matrix g hg n) := by
  rw [← degree_eq,← matrix_eq]
  exact transpose_degree _ _ (Verification.PathRecursiveComplex.z_matrix_degree g 0 hg (by simp) n)

theorem matrix_square (g : R) (hg : g*g=1) (n : ℕ) : matrix g hg n*matrix g hg n=0 := by
  rw [← matrix_eq]
  exact transpose_square _ (z_recursive_square g 0 hg (by simp) n)

noncomputable def complex (g : R) (hg : g*g=1) (n : ℕ) : CochainComplex (ModuleCat R) ℤ :=
  matrixComplex (degree n) (matrix g hg n) (matrix_degree g hg n) (matrix_square g hg n)

noncomputable def recursiveIso (g : R) (hg : g*g=1) (n : ℕ) :
    complex g hg n ≅ Verification.PathRecursiveChain.zComplex g 0 hg (by simp) n :=
  eqToIso (by
    unfold complex Verification.PathRecursiveChain.zComplex
    congr 1
    · exact (degree_eq n).symm
    · exact (matrix_eq g hg n).symm)

noncomputable def homologyBasis (g : R) (hg : g*g=1) (n : ℕ) :
    Basis (Fin (n+4)) R ((complex g hg n).homology 0) :=
  (Verification.PathActualFirstCokernel.zBasis g hg (n+2)).map
    (((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) 0).mapIso
      (recursiveIso g hg n) ≪≫ Verification.PathRecursiveChain.zHomologyZero g hg n).symm.toLinearEquiv)

#print axioms degree
#print axioms degree_eq
#print axioms matrix
#print axioms matrix_eq
#print axioms matrix_degree
#print axioms matrix_square
#print axioms complex
#print axioms recursiveIso
#print axioms homologyBasis

end Verification.PathZPureBlock
