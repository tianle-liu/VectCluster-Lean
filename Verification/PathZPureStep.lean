/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathZPureBlock
import Verification.BoolCopyHomologyBasis
import Verification.PureContractionTransfer

/-!
# Path Z Pure Step

The original Z endpoint recursion constructs its actual normalized
contraction from the already constructed two shorter path contractions.
-/

namespace Verification.PathZPureStep

open Classical Verification.PathPureContractionData Verification.PathStratumGrading
  Verification.PathEndpointCoordinates Verification.PathActualConeMatrices
  Verification.PathRecursiveDegreeCoefficients Verification.PathRecursiveComplex
  Verification.PathFullComplex Verification.GradedPerturbation

variable {R : Type} [CommRing R]

noncomputable def step (g : R) (hg : g*g=1) (n : ℕ)
    (T : Data (fun x => -degree x) (zMatrix g 0 n).transpose)
    (U : Data (fun x => -degree x) (zMatrix g 0 (n+1)).transpose) :
    Data (fun x => -degree x) (zMatrix g 0 (n+2)).transpose := by
  let V := Verification.BoolMatrixCopies.contraction (fun x => -degree x) (zMatrix g 0 (n+1)).transpose U
  let F := Verification.PureConeInductionStep.step
    (fun x => -degree x) (fun x => -degree x.2) (zMatrix g 0 n).transpose
    (Verification.BoolMatrixCopies.copy (zMatrix g 0 (n+1)).transpose)
    (zConnectingMatrix g 0 hg (by simp) n).transpose T V
    (Verification.PathZPureBlock.matrix_degree g hg n) (Verification.PathZPureBlock.matrix_square g hg n)
    (Verification.PathFirstHomology.zHomologyBasis g hg n)
    (Verification.BoolCopyHomologyBasis.homologyBasis _ _ U
      (Verification.PathFirstHomology.zHomologyBasis g hg (n+1)))
    (Verification.PathZPureBlock.homologyBasis g hg n) (by omega)
  have F' : Data (fun x => -zDegree n x) (zRecursiveMatrix g 0 hg (by simp) n).transpose := by
    rw [Verification.PathZPureBlock.degree_eq,Verification.PathZPureBlock.matrix_eq]
    exact F
  exact Verification.PureContractionTransfer.transfer _ _
    (Verification.MatrixDualCoordinates.dualEquiv (zChange g 0 hg (by simp) n))
    (Verification.MatrixDualCoordinates.dual_degree degree (zDegree n) _
      (z_change_inverse_degree g 0 hg (by simp) n))
    (Verification.MatrixDualCoordinates.dual_inverse_degree degree (zDegree n) _
      (z_change_degree g 0 hg (by simp) n))
    (zMatrix g 0 (n+2)).transpose _
    (transpose_degree _ _ (zMatrix_degree g 0 (n+2)))
    (transpose_square _ (zMatrix_squared g 0 (n+2) hg (by simp)))
    (Verification.MatrixDualComplex.dual_intertwining _ _ _ (z_change_differential g 0 hg (by simp) n)) F'

#print axioms step

end Verification.PathZPureStep
