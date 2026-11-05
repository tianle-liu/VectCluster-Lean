/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PureConeInductionStep
import Verification.PathRecursiveChain

/-!
# Path Y Pure Block

Literal Y recursive chain blocks and their genuine degree-zero homology
basis. The degree and matrix equalities are proved from the original recursion.
-/

namespace Verification.PathYPureBlock

open Classical CategoryTheory Verification.GradedPerturbation Verification.PathEndpointWords
  Verification.PathNormalizedBasis Verification.PathStratumGrading
  Verification.PathEndpointCoordinates Verification.PathActualConeMatrices
  Verification.PathRecursiveDegreeCoefficients Verification.PathFullComplex

variable {R : Type} [CommRing R]

def degree (m : ℕ) : YRecursiveIndex m → ℤ :=
  Verification.LowerConeRetraction.degree (fun x => -Verification.PathStratumGrading.degree x)
    (fun x => -Verification.PathStratumGrading.degree x)

theorem degree_eq (m : ℕ) : (fun x => -yDegree m x)=degree m := by
  funext x
  cases x with
  | inl x => change -(Verification.PathStratumGrading.degree x+1)= -Verification.PathStratumGrading.degree x-1; omega
  | inr x => rfl

noncomputable def matrix (g : R) (hg : g*g=1) (m : ℕ) : Matrix (YRecursiveIndex m) (YRecursiveIndex m) R :=
  Matrix.fromBlocks (yMatrix g 0 m).transpose 0 (yConnectingMatrix g 0 hg (by simp) m).transpose
    (zMatrix g 0 (2*m+1)).transpose

theorem matrix_eq (g : R) (hg : g*g=1) (m : ℕ) :
    (yRecursiveMatrix g 0 hg (by simp) m).transpose=matrix g hg m :=
  Verification.PathRecursiveChain.y_chain_blocks g 0 hg (by simp) m

theorem matrix_degree (g : R) (hg : g*g=1) (m : ℕ) : Homogeneous (degree m) 1 (matrix g hg m) := by
  rw [← degree_eq,← matrix_eq]
  exact transpose_degree _ _ (Verification.PathRecursiveComplex.y_matrix_degree g 0 hg (by simp) m)

theorem matrix_square (g : R) (hg : g*g=1) (m : ℕ) : matrix g hg m*matrix g hg m=0 := by
  rw [← matrix_eq]
  exact transpose_square _ (y_recursive_square g 0 hg (by simp) m)

noncomputable def complex (g : R) (hg : g*g=1) (m : ℕ) : CochainComplex (ModuleCat R) ℤ :=
  matrixComplex (degree m) (matrix g hg m) (matrix_degree g hg m) (matrix_square g hg m)

noncomputable def recursiveIso (g : R) (hg : g*g=1) (m : ℕ) :
    complex g hg m ≅ Verification.PathRecursiveChain.yComplex g 0 hg (by simp) m :=
  eqToIso (by
    unfold complex Verification.PathRecursiveChain.yComplex
    congr 1
    · exact (degree_eq m).symm
    · exact (matrix_eq g hg m).symm)

noncomputable def homologyBasis (g : R) (hg : g*g=1) (m : ℕ) :
    Basis (Fin (m+2)) R ((complex g hg m).homology 0) :=
  (Verification.PathActualFirstCokernel.yBasis g hg (m+1)).map
    (((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) 0).mapIso
      (recursiveIso g hg m) ≪≫ Verification.PathRecursiveChain.yHomologyZero g hg m).symm.toLinearEquiv)

#print axioms degree
#print axioms degree_eq
#print axioms matrix
#print axioms matrix_eq
#print axioms matrix_degree
#print axioms matrix_square
#print axioms complex
#print axioms recursiveIso
#print axioms homologyBasis

end Verification.PathYPureBlock
