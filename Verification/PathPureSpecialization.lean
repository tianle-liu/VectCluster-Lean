/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathFullHomology
import Verification.PathScalarNaturality
import Verification.PathGradedMatrices

/-!
# Path Pure Specialization

A genuine weight-preserving pure contraction with coefficient degree zero.
The scalar projection rho=0 is applied to its matrices, so arbitrary choices
in the previous splitting cannot insert positive-degree coefficient terms.
-/

namespace Verification.PathPureSpecialization

open Verification.PathCoefficientRing Verification.PathCoefficientGrading
  Verification.GradedPerturbation Verification.FinitePerturbation Verification.PathFullHomology
  Verification.PathEndpointCoordinates Verification.PathWeightFiltration

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem projection_map (A H : Matrix ι ι Coeff) :
    pureProjection (A.map pure) (H.map pure)=(pureProjection A H).map pure := by
  simp only [pureProjection,Matrix.map_sub pure (map_sub pure),
    Matrix.map_one pure (map_zero pure) (map_one pure),Matrix.map_mul]

noncomputable def data (d : ι → ℤ) (w : ι → ℕ) (A : Matrix ι ι Coeff)
    (T : Verification.WeightedPureContraction.Data d w A) (hA : A.map pure=A) :
    Verification.WeightedPureContraction.Data d w A where
  differential_degree := T.differential_degree
  differential_square := T.differential_square
  homotopy := T.homotopy.map pure
  homotopy_degree i j hij := by rw [Matrix.map_apply,T.homotopy_degree i j hij,map_zero]
  homotopy_square := by rw [← Matrix.map_mul,T.homotopy_square,Matrix.map_zero pure (map_zero pure)]
  homotopy_regular := by
    have hh := congrArg (fun M : Matrix ι ι Coeff => M.map pure) T.homotopy_regular
    simpa only [Matrix.map_mul,hA] using hh
  generalized := by
    have hh := congrArg (fun M : Matrix ι ι Coeff => M.map pure) T.generalized
    simpa only [Matrix.map_mul,hA] using hh
  supported i j hi := by
    have hp := projection_map A T.homotopy
    rw [hA] at hp
    rw [hp,Matrix.map_apply,T.supported i j hi,map_zero]
  weight_preserving i j hij := by rw [Matrix.map_apply,T.weight_preserving i j hij,map_zero]

theorem coefficient_degree (d : ι → ℤ) (w : ι → ℕ) (A : Matrix ι ι Coeff)
    (T : Verification.WeightedPureContraction.Data d w A) (hA : A.map pure=A) :
    PathGradedMatrices.Homogeneous (fun i=>(w i:ℤ)) (fun i=>(w i:ℤ))
      (data d w A T hA).homotopy := by
  intro i j
  by_cases he : w i=w j
  · change PathCoefficientGrading.Homogeneous ((w i:ℤ)-w j) (pure (T.homotopy i j))
    rw [he,sub_self]
    exact pure_homogeneous _
  · rw [(data d w A T hA).weight_preserving i j he]
    exact homogeneous_zero _

theorem z_pure_matrix (n : ℕ) : ((zMatrix g 0 n).transpose).map pure=(zMatrix g 0 n).transpose := by
  rw [Matrix.transpose_map,Verification.PathScalarNaturality.z_matrix,pure_g,map_zero]

theorem y_pure_matrix (a : ℕ) : ((yMatrix g 0 a).transpose).map pure=(yMatrix g 0 a).transpose := by
  rw [Matrix.transpose_map,Verification.PathScalarNaturality.y_matrix,pure_g,map_zero]

noncomputable def zData (n : ℕ) := data _ _ _ (zWeighted g g_square n) (z_pure_matrix n)
noncomputable def yData (a : ℕ) := data _ _ _ (yWeighted g g_square a) (y_pure_matrix a)

theorem z_homotopy_degree (n : ℕ) : PathGradedMatrices.Homogeneous (fun i=>(weight i:ℤ))
    (fun i=>(weight i:ℤ)) (zData n).homotopy :=
  coefficient_degree _ _ _ (zWeighted g g_square n) (z_pure_matrix n)

theorem y_homotopy_degree (a : ℕ) : PathGradedMatrices.Homogeneous (fun i=>(weight i:ℤ))
    (fun i=>(weight i:ℤ)) (yData a).homotopy :=
  coefficient_degree _ _ _ (yWeighted g g_square a) (y_pure_matrix a)

#print axioms projection_map
#print axioms data
#print axioms coefficient_degree
#print axioms z_pure_matrix
#print axioms y_pure_matrix
#print axioms zData
#print axioms yData
#print axioms z_homotopy_degree
#print axioms y_homotopy_degree

end Verification.PathPureSpecialization
