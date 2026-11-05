/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathPureSpecialization
import Verification.PathMatrixCoefficientGrading
import Verification.PathGradedCancellation
import Verification.FilteredZeroReduction

/-!
# Path Graded Full Reduction

The actual all-length full-rho reductions now carry the required scalar
grading on the homotopy, inclusion and retraction. The residual differential
is the already proved zero differential on the pure survivor projector.
-/

namespace Verification.PathGradedFullReduction

open Verification.PathCoefficientRing Verification.PathCoefficientGrading
  Verification.PathEndpointCoordinates Verification.PathStratumGrading Verification.PathFullComplex
  Verification.PathWeightFiltration Verification.GradedPerturbation Verification.FinitePerturbation

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem constant_matrix (w : ι → ℕ) (A : Matrix ι ι Coeff) (hA : A.map pure=A)
    (hw : ∀ i j,w i≠w j → A i j=0) :
    PathGradedMatrices.Homogeneous (fun i=>(w i:ℤ)) (fun i=>(w i:ℤ)) A := by
  intro i j
  by_cases he : w i=w j
  · change PathCoefficientGrading.Homogeneous ((w i:ℤ)-w j) (A i j)
    rw [he,sub_self]
    have hentry := congrArg (fun M : Matrix ι ι Coeff => M i j) hA
    change pure (A i j)=A i j at hentry
    rw [← hentry]
    exact pure_homogeneous _
  · rw [hw i j he]
    exact homogeneous_zero _

variable (d : ι → ℤ) (w : ι → ℕ) (A D : Matrix ι ι Coeff)
variable (P : Verification.WeightedPureContraction.Data d w A)
variable (hd : GradedPerturbation.Homogeneous d 1 D) (hD : D*D=0)
variable (b : ℕ) (hw : ∀ i,w i≤b) (hV : ∀ i j,w i≤w j → (D-A) i j=0)
noncomputable def reduction : Verification.LowerConeRetraction.Data d D (pureProjection A P.homotopy) := by
  let V := D-A
  have he : A+V=D := by dsimp [V]; abel
  let F := Verification.PerturbedHomologyModel.filteredRetraction d A P.homotopy V
    P.differential_degree P.homotopy_degree
    (GradedPerturbation.homogeneous_sub d 1 D A hd P.differential_degree)
    P.differential_square P.homotopy_square P.homotopy_regular P.generalized
    (by rw [he]; exact hD) w b hw P.weight_preserving hV
  have hp := pureProjection_square A P.homotopy P.differential_square P.homotopy_square
    P.homotopy_regular P.generalized
  exact {
    differential := F.differential
    inclusion := F.inclusion
    retraction := F.retraction
    homotopy := F.homotopy
    square := F.square
    inclusion_chain := by simpa only [he] using F.inclusion_chain
    retraction_chain := by simpa only [he] using F.retraction_chain
    retract := F.retract
    homotopy_identity := by simpa only [he] using F.homotopy_identity
    homotopy_square := F.homotopy_square
    homotopy_regular := by simpa only [he] using F.homotopy_regular
    degreeD := hd
    squareD := hD
    degreeS := F.degreeS
    degreeI := F.degreeI
    degreeJ := F.degreeJ
    degreeH := F.degreeH
    retraction_support := F.retraction_support
    differential_support := F.differential_support
    right_support := Verification.TransposeReduction.residual_right A P.homotopy V _ hp
    projection_degree := Verification.PureDegreeSurvivors.projection_degree d A P.homotopy
      P.differential_degree P.homotopy_degree
    projection_square := hp }

theorem residual_zero : (reduction d w A D P hd hD b hw hV).differential=0 :=
  Verification.SingleDegreeResidual.differential_zero d _ _
    (reduction d w A D P hd hD b hw hV).degreeS
    (reduction d w A D P hd hD b hw hV).differential_support
    (reduction d w A D P hd hD b hw hV).right_support P.supported

variable (hcA : PathGradedMatrices.Homogeneous (fun i=>(w i:ℤ)) (fun i=>(w i:ℤ)) A)
variable (hcD : PathGradedMatrices.Homogeneous (fun i=>(w i:ℤ)) (fun i=>(w i:ℤ)) D)
variable (hcH : PathGradedMatrices.Homogeneous (fun i=>(w i:ℤ)) (fun i=>(w i:ℤ)) P.homotopy)

include hcA hcD hcH in
theorem coefficients :
    let F := reduction d w A D P hd hD b hw hV
    PathGradedMatrices.Homogeneous (fun i=>(w i:ℤ)) (fun i=>(w i:ℤ)) F.homotopy ∧
    PathGradedMatrices.Homogeneous (fun i=>(w i:ℤ)) (fun i=>(w i:ℤ)) F.inclusion ∧
    PathGradedMatrices.Homogeneous (fun i=>(w i:ℤ)) (fun i=>(w i:ℤ)) F.retraction := by
  let V := D-A
  have hcV := PathGradedMatrices.sub (fun i=>(w i:ℤ)) (fun i=>(w i:ℤ)) D A hcD hcA
  have hn := Verification.ChainCancellation.raising_matrix_nilpotent (V*P.homotopy) w b hw
    (preserving_raising_products P.homotopy V w P.weight_preserving hV).1
  exact ⟨PathGradedCancellation.homotopy _ _ _ hcH hcV (b+1) hn,
    PathGradedCancellation.inclusion _ _ _ _ hcA hcH hcV (b+1) hn,
    PathGradedCancellation.retraction _ _ _ _ hcA hcH hcV (b+1) hn⟩

noncomputable def zReduction (n : ℕ) :=
  reduction _ _ _ _ (Verification.PathPureSpecialization.zData n)
    (transpose_degree _ _ (zMatrix_degree g rho n)) (transpose_square _ (zMatrix_squared g rho n g_square rho_relation))
    (n+1) (Verification.PathWeightBounds.z_weight_bound n)
    (fun i j hij => by simpa only [Matrix.transpose_sub] using
      Verification.PathMatrixPerturbation.z_chain_difference_strict g rho n i j hij)

noncomputable def yReduction (a : ℕ) :=
  reduction _ _ _ _ (Verification.PathPureSpecialization.yData a)
    (transpose_degree _ _ (yMatrix_degree g rho a)) (transpose_square _ (yMatrix_squared g rho a g_square rho_relation))
    (2*a) (Verification.PathWeightBounds.y_weight_bound a)
    (fun i j hij => by simpa only [Matrix.transpose_sub] using
      Verification.PathMatrixPerturbation.y_chain_difference_strict g rho a i j hij)

theorem z_coefficients (n : ℕ) :
    PathGradedMatrices.Homogeneous (fun i=>(weight i:ℤ)) (fun i=>(weight i:ℤ)) (zReduction n).homotopy ∧
    PathGradedMatrices.Homogeneous (fun i=>(weight i:ℤ)) (fun i=>(weight i:ℤ)) (zReduction n).inclusion ∧
    PathGradedMatrices.Homogeneous (fun i=>(weight i:ℤ)) (fun i=>(weight i:ℤ)) (zReduction n).retraction :=
  coefficients _ _ _ _ _ _ _ _ _ _
    (constant_matrix _ _ (Verification.PathPureSpecialization.z_pure_matrix n)
      (fun i j hij=>Verification.PathPureMatrixWeight.z_matrix_exact_weight g n j i hij.symm))
    (Verification.PathMatrixCoefficientGrading.z_chain_degree n)
    (Verification.PathPureSpecialization.z_homotopy_degree n)

theorem y_coefficients (a : ℕ) :
    PathGradedMatrices.Homogeneous (fun i=>(weight i:ℤ)) (fun i=>(weight i:ℤ)) (yReduction a).homotopy ∧
    PathGradedMatrices.Homogeneous (fun i=>(weight i:ℤ)) (fun i=>(weight i:ℤ)) (yReduction a).inclusion ∧
    PathGradedMatrices.Homogeneous (fun i=>(weight i:ℤ)) (fun i=>(weight i:ℤ)) (yReduction a).retraction :=
  coefficients _ _ _ _ _ _ _ _ _ _
    (constant_matrix _ _ (Verification.PathPureSpecialization.y_pure_matrix a)
      (fun i j hij=>Verification.PathPureMatrixWeight.y_matrix_exact_weight g a j i hij.symm))
    (Verification.PathMatrixCoefficientGrading.y_chain_degree a)
    (Verification.PathPureSpecialization.y_homotopy_degree a)

theorem z_residual_zero (n : ℕ) : (zReduction n).differential=0 :=
  residual_zero _ _ _ _ _ _ _ _ _ _

theorem y_residual_zero (a : ℕ) : (yReduction a).differential=0 :=
  residual_zero _ _ _ _ _ _ _ _ _ _

#print axioms constant_matrix
#print axioms reduction
#print axioms residual_zero
#print axioms coefficients
#print axioms zReduction
#print axioms yReduction
#print axioms z_coefficients
#print axioms y_coefficients
#print axioms z_residual_zero
#print axioms y_residual_zero

end Verification.PathGradedFullReduction
