/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathYPureBlock
import Verification.PureContractionTransfer

/-!
# Path Y Pure Step

The original Y endpoint recursion now constructs its actual normalized
contraction from the already constructed shorter Y and Z contractions.
-/

namespace Verification.PathYPureStep

open Classical Verification.PathPureContractionData Verification.PathStratumGrading
  Verification.PathEndpointCoordinates Verification.PathActualConeMatrices
  Verification.PathRecursiveDegreeCoefficients Verification.PathRecursiveComplex
  Verification.PathFullComplex Verification.GradedPerturbation

variable {R : Type} [CommRing R]

noncomputable def step (g : R) (hg : g*g=1) (m : ℕ)
    (T : Data (fun x => -degree x) (yMatrix g 0 m).transpose)
    (U : Data (fun x => -degree x) (zMatrix g 0 (2*m+1)).transpose) :
    Data (fun x => -degree x) (yMatrix g 0 (m+1)).transpose := by
  let F := Verification.PureConeInductionStep.step
    (fun x => -degree x) (fun x => -degree x) (yMatrix g 0 m).transpose
    (zMatrix g 0 (2*m+1)).transpose (yConnectingMatrix g 0 hg (by simp) m).transpose T U
    (Verification.PathYPureBlock.matrix_degree g hg m) (Verification.PathYPureBlock.matrix_square g hg m)
    (Verification.PathFirstHomology.yHomologyBasis g hg m)
    (Verification.PathFirstHomology.zHomologyBasis g hg (2*m+1))
    (Verification.PathYPureBlock.homologyBasis g hg m) (by omega)
  have F' : Data (fun x => -yDegree m x) (yRecursiveMatrix g 0 hg (by simp) m).transpose := by
    rw [Verification.PathYPureBlock.degree_eq,Verification.PathYPureBlock.matrix_eq]
    exact F
  exact Verification.PureContractionTransfer.transfer _ _
    (Verification.MatrixDualCoordinates.dualEquiv (yChange g 0 hg (by simp) m))
    (Verification.MatrixDualCoordinates.dual_degree degree (yDegree m) _
      (y_change_inverse_degree g 0 hg (by simp) m))
    (Verification.MatrixDualCoordinates.dual_inverse_degree degree (yDegree m) _
      (y_change_degree g 0 hg (by simp) m))
    (yMatrix g 0 (m+1)).transpose _
    (transpose_degree _ _ (yMatrix_degree g 0 (m+1)))
    (transpose_square _ (yMatrix_squared g 0 (m+1) hg (by simp)))
    (Verification.MatrixDualComplex.dual_intertwining _ _ _ (y_change_differential g 0 hg (by simp) m)) F'

#print axioms step

end Verification.PathYPureStep
