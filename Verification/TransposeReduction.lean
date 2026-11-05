/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PerturbedHomologyModel

/-!
# Transpose Reduction

Literal transposition of the constructed finite cancellation, reversing the
cellular grading and interchanging inclusion with retraction.  The extra
right-support identities needed by the dual survivor module are proved for
the actual finite perturbation formulas, not assumed for those formulas.
-/

namespace Verification.TransposeReduction

open Verification.FinitePerturbation Verification.GradedPerturbation
open Verification.PerturbedHomologyModel

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- Transposition reverses cellular grading and preserves differential degree. -/
theorem homogeneous_transpose (deg : ι → ℤ) (k : ℤ) (M : Matrix ι ι R)
    (hM : Homogeneous deg k M) : Homogeneous (fun i => -deg i) k M.transpose := by
  intro i j hij
  change -deg i ≠ -deg j+k at hij
  exact hM j i (by intro he; apply hij; omega)

/-- Every algebraic homotopy identity transposes, exchanging the two chain maps. -/
def transposeRetraction (D P : Matrix ι ι R) (T : MatrixRetraction D P) :
    MatrixRetraction D.transpose P.transpose where
  differential := T.differential.transpose
  inclusion := T.retraction.transpose
  retraction := T.inclusion.transpose
  homotopy := T.homotopy.transpose
  square := by simpa only [Matrix.transpose_mul, Matrix.transpose_zero] using congrArg Matrix.transpose T.square
  inclusion_chain := by
    simpa only [Matrix.transpose_mul] using congrArg Matrix.transpose T.retraction_chain
  retraction_chain := by
    simpa only [Matrix.transpose_mul] using congrArg Matrix.transpose T.inclusion_chain
  retract := by simpa only [Matrix.transpose_mul] using congrArg Matrix.transpose T.retract
  homotopy_identity := by
    have ht := congrArg Matrix.transpose T.homotopy_identity
    simp only [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one] at ht
    rw [ht]
    abel
  homotopy_square := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_zero] using congrArg Matrix.transpose T.homotopy_square
  homotopy_regular := by
    simpa only [Matrix.transpose_mul, mul_assoc] using congrArg Matrix.transpose T.homotopy_regular

/-- The actual dual graded retraction, with the support needed by its fixed module. -/
def transposeGraded (deg : ι → ℤ) (D P : Matrix ι ι R) (T : GradedRetraction deg D P)
    (hIP : T.inclusion*P=T.inclusion) (hSP : T.differential*P=T.differential) :
    GradedRetraction (fun i => -deg i) D.transpose P.transpose where
  toMatrixRetraction := transposeRetraction D P T.toMatrixRetraction
  degreeD := homogeneous_transpose deg 1 D T.degreeD
  squareD := by simpa only [Matrix.transpose_mul, Matrix.transpose_zero] using congrArg Matrix.transpose T.squareD
  degreeS := homogeneous_transpose deg 1 T.differential T.degreeS
  degreeI := homogeneous_transpose deg 0 T.retraction T.degreeJ
  degreeJ := homogeneous_transpose deg 0 T.inclusion T.degreeI
  degreeH := homogeneous_transpose deg (-1) T.homotopy T.degreeH
  retraction_support := by simpa only [Matrix.transpose_mul] using congrArg Matrix.transpose hIP
  differential_support := by simpa only [Matrix.transpose_mul] using congrArg Matrix.transpose hSP

/-- A genuine homotopy equivalence of the transposed source and residual complexes. -/
noncomputable def transposeEquivalence (deg : ι → ℤ) (D P : Matrix ι ι R)
    (T : GradedRetraction deg D P)
    (hIP : T.inclusion*P=T.inclusion) (hSP : T.differential*P=T.differential) :
    HomotopyEquiv (sourceComplex (fun i => -deg i) _ _ (transposeGraded deg D P T hIP hSP))
      (targetComplex (fun i => -deg i) _ _ (transposeGraded deg D P T hIP hSP)) :=
  homotopyEquiv _ _ _ _

/-- The corrected inclusion of the finite cancellation really has right pure-homology support. -/
theorem corrected_inclusion_right (U H V : Matrix ι ι R) (q : (Matrix ι ι R)ˣ)
    (hP : pureProjection U H*pureProjection U H=pureProjection U H) :
    correctedInclusion U H V q*pureProjection U H=correctedInclusion U H V q := by
  change (pureProjection U H-H*correction V q*pureProjection U H)*pureProjection U H=_
  rw [sub_mul, hP, mul_assoc, hP]
  rfl

/-- The computed residual also has right pure-homology support. -/
theorem residual_right (U H V : Matrix ι ι R) (q : (Matrix ι ι R)ˣ)
    (hP : pureProjection U H*pureProjection U H=pureProjection U H) :
    residualDifferential U H V q*pureProjection U H=residualDifferential U H V q := by
  change (pureProjection U H*correction V q*pureProjection U H)*pureProjection U H=_
  rw [mul_assoc, hP]
  rfl

variable (deg : ι → ℤ) (U H V : Matrix ι ι R)
variable (hdU : Homogeneous deg 1 U) (hdH : Homogeneous deg (-1) H) (hdV : Homogeneous deg 1 V)
variable (hU : U*U=0) (hHH : H*H=0) (hHUH : H*U*H=H) (hUHU : U*H*U=U)
variable (hD : (U+V)*(U+V)=0) (w : ι → ℕ) (b : ℕ)
variable (hw : ∀ i, w i ≤ b) (hH : ∀ i j, w i ≠ w j → H i j=0)
variable (hV : ∀ i j, w i ≤ w j → V i j=0)

/-- No additional support hypothesis is needed for the actual finite cancellation. -/
noncomputable def transposedFiltered :
    GradedRetraction (fun i => -deg i) (U+V).transpose (pureProjection U H).transpose :=
  transposeGraded deg (U+V) (pureProjection U H)
    (filteredRetraction deg U H V hdU hdH hdV hU hHH hHUH hUHU hD w b hw hH hV)
    (corrected_inclusion_right U H V _ (pureProjection_square U H hU hHH hHUH hUHU))
    (residual_right U H V _ (pureProjection_square U H hU hHH hHUH hUHU))

#print axioms homogeneous_transpose
#print axioms transposeRetraction
#print axioms transposeGraded
#print axioms transposeEquivalence
#print axioms corrected_inclusion_right
#print axioms residual_right
#print axioms transposedFiltered

end Verification.TransposeReduction
