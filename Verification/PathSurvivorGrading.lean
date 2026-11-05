/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathWeightedSurvivors
import Verification.PathGradedFullReduction
import Verification.WeightedFixedBasis

/-!
# Path Survivor Grading

Exact weight and scalar degree of the original surviving path basis.
The pure normalized projection and the explicit signed representatives supply
all assertions internally.
-/

namespace Verification.PathSurvivorGrading

open Verification.PathCoefficientRing Verification.PathCoefficientGrading
  Verification.PathEndpointWords Verification.PathEndpointCoordinates Verification.PathWeightFiltration
  Verification.FinitePerturbation Verification.PathPureSpecialization
  Verification.PathCokernel Verification.PathWeightedSurvivors

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem projection_preserves (w : ι → ℕ) (A H : Matrix ι ι Coeff)
    (hA : ∀i j,w i≠w j → A i j=0) (hH : ∀i j,w i≠w j → H i j=0) :
    ∀i j,w i≠w j → pureProjection A H i j=0 := by
  let v : ι → ℤ := fun i=>w i
  have ha : Verification.GradedPerturbation.Homogeneous v 0 A := by
    intro i j hij
    exact hA i j (by intro he;apply hij;change (w i:ℤ)=(w j:ℤ)+0;rw [he,add_zero])
  have hh : Verification.GradedPerturbation.Homogeneous v 0 H := by
    intro i j hij
    exact hH i j (by intro he;apply hij;change (w i:ℤ)=(w j:ℤ)+0;rw [he,add_zero])
  have hp : Verification.GradedPerturbation.Homogeneous v 0 (pureProjection A H) :=
    Verification.GradedPerturbation.homogeneous_sub v 0 _ _
      (Verification.GradedPerturbation.homogeneous_sub v 0 _ _
        (Verification.GradedPerturbation.homogeneous_one v)
        (by simpa using Verification.GradedPerturbation.homogeneous_mul v 0 0 A H ha hh))
      (by simpa using Verification.GradedPerturbation.homogeneous_mul v 0 0 H A hh ha)
  intro i j hij
  exact hp i j (by change (w i:ℤ)≠(w j:ℤ)+0;omega)

noncomputable def zProjection (n : ℕ) := pureProjection (zMatrix g 0 n).transpose (zData n).homotopy
noncomputable def yProjection (a : ℕ) := pureProjection (yMatrix g 0 a).transpose (yData a).homotopy

noncomputable def zBasis (n : ℕ) := PathWeightedSurvivors.zBasis g g_square n (zData n).toData
noncomputable def yBasis (a : ℕ) := PathWeightedSurvivors.yBasis g g_square a (yData a).toData

theorem zProjection_weight (n : ℕ) : ∀i j,PathWeightFiltration.weight i≠PathWeightFiltration.weight j → zProjection n i j=0 :=
  projection_preserves PathWeightFiltration.weight _ _
    (fun i j hij=>Verification.PathPureMatrixWeight.z_matrix_exact_weight g n j i hij.symm)
    (zData n).weight_preserving

theorem yProjection_weight (a : ℕ) : ∀i j,PathWeightFiltration.weight i≠PathWeightFiltration.weight j → yProjection a i j=0 :=
  projection_preserves PathWeightFiltration.weight _ _
    (fun i j hij=>Verification.PathPureMatrixWeight.y_matrix_exact_weight g a j i hij.symm)
    (yData a).weight_preserving

theorem zProjection_degree (n : ℕ) : PathGradedMatrices.Homogeneous
    (fun i=>(PathWeightFiltration.weight i:ℤ)) (fun i=>(PathWeightFiltration.weight i:ℤ)) (zProjection n) :=
  PathGradedCancellation.projection _ _ _
    (PathGradedFullReduction.constant_matrix _ _ (z_pure_matrix n)
      (fun i j hij=>Verification.PathPureMatrixWeight.z_matrix_exact_weight g n j i hij.symm))
    (z_homotopy_degree n)

theorem yProjection_degree (a : ℕ) : PathGradedMatrices.Homogeneous
    (fun i=>(PathWeightFiltration.weight i:ℤ)) (fun i=>(PathWeightFiltration.weight i:ℤ)) (yProjection a) :=
  PathGradedCancellation.projection _ _ _
    (PathGradedFullReduction.constant_matrix _ _ (y_pure_matrix a)
      (fun i j hij=>Verification.PathPureMatrixWeight.y_matrix_exact_weight g a j i hij.symm))
    (y_homotopy_degree a)

theorem zBasis_weight (n : ℕ) (k : Weight false (n+1)) (i) (hi : PathWeightFiltration.weight i≠k.val.val) :
    (zBasis n k).val i=0 := by
  rw [zBasis,zBasis_entry]
  rw [show pureProjection (zMatrix g 0 n).transpose (zData n).homotopy i
    (Verification.PathFirstDegreeCoordinates.zZeroIndex n (representative k)).val=0 from
      zProjection_weight n i _ (by rwa [zZeroIndex_weight,PathSignedRepresentatives.representative_count]),zero_mul]

theorem yBasis_weight (a : ℕ) (k : Weight true (2*a)) (i) (hi : PathWeightFiltration.weight i≠k.val.val) :
    (yBasis a k).val i=0 := by
  rw [yBasis,yBasis_entry]
  rw [show pureProjection (yMatrix g 0 a).transpose (yData a).homotopy i
    (Verification.PathFirstDegreeCoordinates.yZeroIndex a (representative k)).val=0 from
      yProjection_weight a i _ (by rwa [yZeroIndex_weight,PathSignedRepresentatives.representative_count]),zero_mul]

theorem zBasis_degree (n : ℕ) (k : Weight false (n+1)) (i) :
    PathCoefficientGrading.Homogeneous ((PathWeightFiltration.weight i:ℤ)-k.val.val) ((zBasis n k).val i) := by
  rw [zBasis,zBasis_entry]
  have hp := zProjection_degree n i (Verification.PathFirstDegreeCoordinates.zZeroIndex n (representative k)).val
  dsimp only at hp
  rw [zZeroIndex_weight,PathSignedRepresentatives.representative_count] at hp
  simpa using homogeneous_mul hp (PathSignedRepresentatives.scale_degree (representative k))

theorem yBasis_degree (a : ℕ) (k : Weight true (2*a)) (i) :
    PathCoefficientGrading.Homogeneous ((PathWeightFiltration.weight i:ℤ)-k.val.val) ((yBasis a k).val i) := by
  rw [yBasis,yBasis_entry]
  have hp := yProjection_degree a i (Verification.PathFirstDegreeCoordinates.yZeroIndex a (representative k)).val
  dsimp only at hp
  rw [yZeroIndex_weight,PathSignedRepresentatives.representative_count] at hp
  simpa using homogeneous_mul hp (PathSignedRepresentatives.scale_degree (representative k))

#print axioms projection_preserves
#print axioms zProjection
#print axioms yProjection
#print axioms zBasis
#print axioms yBasis
#print axioms zProjection_weight
#print axioms yProjection_weight
#print axioms zProjection_degree
#print axioms yProjection_degree
#print axioms zBasis_weight
#print axioms yBasis_weight
#print axioms zBasis_degree
#print axioms yBasis_degree

end Verification.PathSurvivorGrading
