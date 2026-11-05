/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.TwoDegreeResidualPivot
import Verification.SuccessiveContraction
import Verification.ContractionProjectionSupport

/-!
# Recursive Residual Elimination

Complete algebraic elimination of an actual two-degree residual complex.
The free zeroth homology and the rank-balance equivalence construct the pivot;
the resulting contraction is lifted to the original matrix and normalized.
-/

namespace Verification.RecursiveResidualElimination

open CategoryTheory Verification.FinitePerturbation Verification.GradedPerturbation
  Verification.PerturbedHomologyModel Verification.GradedIntegralSplitting

variable {R ι Q : Type} [CommRing R] [Fintype ι] [DecidableEq ι]
variable [AddCommGroup Q] [Module R Q] [Module.Projective R Q]
variable (d : ι → ℤ) (D P : Matrix ι ι R) (T : GradedRetraction d D P)
variable (hdP : Homogeneous d 0 P) (hPP : P*P=P)
variable (hSP : T.differential*P=T.differential)
variable (hP : ∀ i j,d i ≠ -1 → d i ≠ 0 → P i j=0)
variable (h0 : (matrixComplex d D T.degreeD T.squareD).homology 0 ≃ₗ[R] Q)
variable (balance : (fixedModule d P (-1) × Q) ≃ₗ[R] fixedModule d P 0)

noncomputable def residualHomology :
    (targetComplex d D P T).homology 0 ≃ₗ[R] Q :=
  ((homotopyEquiv d D P T).toHomologyIso 0).symm.toLinearEquiv.trans h0

noncomputable def residualInverse : Matrix ι ι R :=
  Verification.TwoDegreeResidualPivot.generalizedInverse d P T.differential T.degreeS hdP hPP
    T.differential_support T.square hP (residualHomology d D P T h0) balance

noncomputable def rawInverse : Matrix ι ι R :=
  T.homotopy+T.inclusion*residualInverse d D P T hdP hPP hP h0 balance*T.retraction

include hSP in
theorem raw_generalized : D*rawInverse d D P T hdP hPP hP h0 balance*D=D :=
  Verification.SuccessiveContraction.generalized D P T.squareD T.toMatrixRetraction _
    (Verification.TwoDegreeResidualPivot.generalized d P T.differential T.degreeS hdP hPP
      T.differential_support hSP T.square hP (residualHomology d D P T h0) balance)

theorem raw_degree : Homogeneous d (-1) (rawInverse d D P T hdP hPP hP h0 balance) := by
  apply homogeneous_add d (-1) _ _ T.degreeH
  have hK := Verification.TwoDegreeResidualPivot.inverse_degree d P T.differential T.degreeS hdP hPP
    T.differential_support T.square hP (residualHomology d D P T h0) balance
  have hIK : Homogeneous d (-1) (T.inclusion*residualInverse d D P T hdP hPP hP h0 balance) := by
    simpa using homogeneous_mul d 0 (-1) _ _ T.degreeI hK
  simpa using homogeneous_mul d (-1) 0 _ _ hIK T.degreeJ

noncomputable def contraction : Matrix ι ι R := normalize D (rawInverse d D P T hdP hPP hP h0 balance)

include hSP in
theorem contraction_square : contraction d D P T hdP hPP hP h0 balance *
    contraction d D P T hdP hPP hP h0 balance=0 :=
  normalize_square D _ (raw_generalized d D P T hdP hPP hSP hP h0 balance)

include hSP in
theorem contraction_generalized : D*contraction d D P T hdP hPP hP h0 balance*D=D :=
  normalize_generalized D _ T.squareD (raw_generalized d D P T hdP hPP hSP hP h0 balance)

include hSP in
theorem contraction_regular : contraction d D P T hdP hPP hP h0 balance*D*
    contraction d D P T hdP hPP hP h0 balance=contraction d D P T hdP hPP hP h0 balance :=
  normalize_regular D _ T.squareD (raw_generalized d D P T hdP hPP hSP hP h0 balance)

theorem contraction_degree : Homogeneous d (-1) (contraction d D P T hdP hPP hP h0 balance) :=
  normalize_degree d D _ T.degreeD (raw_degree d D P T hdP hPP hP h0 balance)

include hdP hPP hP h0 balance in
theorem homology_vanishes (p : ℤ) (hp : p ≠ 0) :
    Limits.IsZero ((matrixComplex d D T.degreeD T.squareD).homology p) :=
  ((homotopyEquiv d D P T).toHomologyIso p).isZero_iff.mpr
    (Verification.TwoDegreeResidualPivot.homology_vanishes d P T.differential T.degreeS hdP hPP
      T.differential_support T.square hP (residualHomology d D P T h0) balance p hp)

include hSP in
theorem projection_supported (i j : ι) (hi : d i ≠ 0) :
    pureProjection D (contraction d D P T hdP hPP hP h0 balance) i j=0 :=
  Verification.ContractionProjectionSupport.projection_row_zero d D _ T.degreeD
    (contraction_degree d D P T hdP hPP hP h0 balance) T.squareD
    (contraction_square d D P T hdP hPP hSP hP h0 balance)
    (contraction_regular d D P T hdP hPP hSP hP h0 balance)
    (contraction_generalized d D P T hdP hPP hSP hP h0 balance)
    (d i) (homology_vanishes d D P T hdP hPP hP h0 balance (d i) hi) i j rfl

#print axioms residualHomology
#print axioms residualInverse
#print axioms rawInverse
#print axioms raw_generalized
#print axioms raw_degree
#print axioms contraction
#print axioms contraction_square
#print axioms contraction_generalized
#print axioms contraction_regular
#print axioms contraction_degree
#print axioms homology_vanishes
#print axioms projection_supported

end Verification.RecursiveResidualElimination
