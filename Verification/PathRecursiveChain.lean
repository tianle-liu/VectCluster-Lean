/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathRecursiveComplex
import Verification.MatrixDualComplex
import Verification.PathFirstHomology

/-!
# Path Recursive Chain

The actual full-rho endpoint recursion for the transposed path chain
complexes. The change of coordinates is the proved inverse transpose, and the
closed summand has homological degree one.
-/

namespace Verification.PathRecursiveChain

open Classical CategoryTheory Verification.GradedPerturbation Verification.PathFullComplex
  Verification.PathRecursiveComplex Verification.PathActualConeMatrices
  Verification.PathRecursiveDegreeCoefficients Verification.PathStratumGrading
  Verification.PathEndpointCoordinates

variable {R : Type} [CommRing R] (g ρ : R) (hg : g*g=1) (hr : (1+g)*ρ=0)

noncomputable def zComplex (n : ℕ) : CochainComplex (ModuleCat R) ℤ :=
  matrixComplex (fun x => -zDegree n x) (zRecursiveMatrix g ρ hg hr n).transpose
    (transpose_degree _ _ (z_matrix_degree g ρ hg hr n))
    (transpose_square _ (z_recursive_square g ρ hg hr n))

noncomputable def yComplex (m : ℕ) : CochainComplex (ModuleCat R) ℤ :=
  matrixComplex (fun x => -yDegree m x) (yRecursiveMatrix g ρ hg hr m).transpose
    (transpose_degree _ _ (y_matrix_degree g ρ hg hr m))
    (transpose_square _ (y_recursive_square g ρ hg hr m))

noncomputable def zIso (n : ℕ) : zChainComplex g ρ (n+2) hg hr ≅ zComplex g ρ hg hr n :=
  Verification.MatrixDualComplex.complexIso degree (zDegree n) (zChange g ρ hg hr n)
    (z_change_degree g ρ hg hr n) (z_change_inverse_degree g ρ hg hr n)
    (zMatrix g ρ (n+2)) (zRecursiveMatrix g ρ hg hr n)
    (zMatrix_degree g ρ (n+2)) (z_matrix_degree g ρ hg hr n)
    (zMatrix_squared g ρ (n+2) hg hr) (z_recursive_square g ρ hg hr n)
    (z_change_differential g ρ hg hr n)

noncomputable def yIso (m : ℕ) : yChainComplex g ρ (m+1) hg hr ≅ yComplex g ρ hg hr m :=
  Verification.MatrixDualComplex.complexIso degree (yDegree m) (yChange g ρ hg hr m)
    (y_change_degree g ρ hg hr m) (y_change_inverse_degree g ρ hg hr m)
    (yMatrix g ρ (m+1)) (yRecursiveMatrix g ρ hg hr m)
    (yMatrix_degree g ρ (m+1)) (y_matrix_degree g ρ hg hr m)
    (yMatrix_squared g ρ (m+1) hg hr) (y_recursive_square g ρ hg hr m)
    (y_change_differential g ρ hg hr m)

theorem z_chain_blocks (n : ℕ) :
    (zRecursiveMatrix g ρ hg hr n).transpose=Matrix.fromBlocks (zMatrix g ρ n).transpose 0
      (zConnectingMatrix g ρ hg hr n).transpose (torusMatrix g ρ (n+1)).transpose := by
  rw [z_recursive_matrix,Matrix.fromBlocks_transpose,Matrix.transpose_zero]

theorem y_chain_blocks (m : ℕ) :
    (yRecursiveMatrix g ρ hg hr m).transpose=Matrix.fromBlocks (yMatrix g ρ m).transpose 0
      (yConnectingMatrix g ρ hg hr m).transpose (zMatrix g ρ (2*m+1)).transpose := by
  rw [y_recursive_matrix,Matrix.fromBlocks_transpose,Matrix.transpose_zero]

noncomputable def zHomologyZero (n : ℕ) :
    (zComplex g 0 hg (by simp) n).homology 0 ≅
      ModuleCat.of R (Verification.PathActualFirstCokernel.ZCokernel g (n+2)) :=
  ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) 0).mapIso
    (zIso g 0 hg (by simp) n)).symm ≪≫ Verification.PathFirstHomology.zHomologyIso g hg (n+2)

noncomputable def yHomologyZero (m : ℕ) :
    (yComplex g 0 hg (by simp) m).homology 0 ≅
      ModuleCat.of R (Verification.PathActualFirstCokernel.YCokernel g (m+1)) :=
  ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) 0).mapIso
    (yIso g 0 hg (by simp) m)).symm ≪≫ Verification.PathFirstHomology.yHomologyIso g hg (m+1)

#print axioms zComplex
#print axioms yComplex
#print axioms zIso
#print axioms yIso
#print axioms z_chain_blocks
#print axioms y_chain_blocks
#print axioms zHomologyZero
#print axioms yHomologyZero

end Verification.PathRecursiveChain
