/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathSurvivorGrading
import Verification.PureRectangularCoefficients

/-!
# Path Survivor Matrices

Literal rectangular splitting onto the proved path survivor basis, with
actual scalar degree target weight minus source weight in both directions.
-/

namespace Verification.PathSurvivorMatrices

open Classical Verification.PathCoefficientRing Verification.PathCoefficientGrading
  Verification.PathEndpointWords Verification.PathEndpointCoordinates Verification.PathNormalizedBasis
  Verification.PathWeightFiltration Verification.FinitePerturbation Verification.PathPureSpecialization
  Verification.PathSurvivorGrading Verification.SurvivorBaseChange Verification.PureRectangularCoefficients


theorem zProjection_map (n : ℕ) : (zProjection n).map pure=zProjection n := by
  have hh : (zData n).homotopy.map pure=(zData n).homotopy := by
    ext i j
    exact pure_twice _
  change (pureProjection (zMatrix g 0 n).transpose (zData n).homotopy).map pure=_
  rw [←projection_map,z_pure_matrix,hh]
  rfl

theorem yProjection_map (a : ℕ) : (yProjection a).map pure=yProjection a := by
  have hh : (yData a).homotopy.map pure=(yData a).homotopy := by
    ext i j
    exact pure_twice _
  change (pureProjection (yMatrix g 0 a).transpose (yData a).homotopy).map pure=_
  rw [←projection_map,y_pure_matrix,hh]
  rfl

theorem zProjection_square (n : ℕ) : zProjection n*zProjection n=zProjection n :=
  pureProjection_square _ _ (zData n).differential_square (zData n).homotopy_square
    (zData n).homotopy_regular (zData n).generalized

theorem yProjection_square (a : ℕ) : yProjection a*yProjection a=yProjection a :=
  pureProjection_square _ _ (yData a).differential_square (yData a).homotopy_square
    (yData a).homotopy_regular (yData a).generalized

noncomputable def zInclusion (n : ℕ) : Matrix (NormalIndex RightNormal n)
    (Verification.PathCokernel.Weight false (n+1)) Coeff := inclusionMatrix (zProjection n) (zBasis n)
noncomputable def yInclusion (a : ℕ) : Matrix (NormalIndex BothNormal (2*a))
    (Verification.PathCokernel.Weight true (2*a)) Coeff := inclusionMatrix (yProjection a) (yBasis a)

noncomputable def zRetraction (n : ℕ) := inverse (zProjection n) (zProjection_square n) (zBasis n)
noncomputable def yRetraction (a : ℕ) := inverse (yProjection a) (yProjection_square a) (yBasis a)

theorem zInclusion_map (n : ℕ) : (zInclusion n).map pure=zInclusion n := by
  ext i k
  change pure (inclusionMatrix (zProjection n) (zBasis n) i k)=inclusionMatrix (zProjection n) (zBasis n) i k
  rw [WeightedFixedBasis.inclusion_entry]
  change pure ((zBasis n k).val i)=(zBasis n k).val i
  rw [zBasis,PathWeightedSurvivors.zBasis_entry,map_mul]
  change pure (zProjection n i _)*pure (Verification.PathSignNormalization.wordScale g (n+1) _)=_
  rw [show pure (zProjection n i (Verification.PathFirstDegreeCoordinates.zZeroIndex n
    (Verification.PathCokernel.representative k)).val)=zProjection n i (Verification.PathFirstDegreeCoordinates.zZeroIndex n
        (Verification.PathCokernel.representative k)).val from
      congrArg (fun M : Matrix (NormalIndex RightNormal n) (NormalIndex RightNormal n) Coeff=>
        M i (Verification.PathFirstDegreeCoordinates.zZeroIndex n
          (Verification.PathCokernel.representative k)).val) (zProjection_map n)]
  simp only [Verification.PathSignNormalization.wordScale,map_pow,pure_g]
  rfl

theorem yInclusion_map (a : ℕ) : (yInclusion a).map pure=yInclusion a := by
  ext i k
  change pure (inclusionMatrix (yProjection a) (yBasis a) i k)=inclusionMatrix (yProjection a) (yBasis a) i k
  rw [WeightedFixedBasis.inclusion_entry]
  change pure ((yBasis a k).val i)=(yBasis a k).val i
  rw [yBasis,PathWeightedSurvivors.yBasis_entry,map_mul]
  change pure (yProjection a i _)*pure (Verification.PathSignNormalization.wordScale g (2*a) _)=_
  rw [show pure (yProjection a i (Verification.PathFirstDegreeCoordinates.yZeroIndex a
    (Verification.PathCokernel.representative k)).val)=yProjection a i (Verification.PathFirstDegreeCoordinates.yZeroIndex a
        (Verification.PathCokernel.representative k)).val from
      congrArg (fun M : Matrix (NormalIndex BothNormal (2*a)) (NormalIndex BothNormal (2*a)) Coeff=>
        M i (Verification.PathFirstDegreeCoordinates.yZeroIndex a
          (Verification.PathCokernel.representative k)).val) (yProjection_map a)]
  simp only [Verification.PathSignNormalization.wordScale,map_pow,pure_g]
  rfl

theorem zInclusion_degree (n : ℕ) : PathGradedMatrices.Homogeneous
    (fun i=>(weight i:ℤ)) (fun k=>(k.val.val:ℤ)) (zInclusion n) := by
  intro i k
  rw [zInclusion,WeightedFixedBasis.inclusion_entry]
  exact zBasis_degree n k i

theorem yInclusion_degree (a : ℕ) : PathGradedMatrices.Homogeneous
    (fun i=>(weight i:ℤ)) (fun k=>(k.val.val:ℤ)) (yInclusion a) := by
  intro i k
  rw [yInclusion,WeightedFixedBasis.inclusion_entry]
  exact yBasis_degree a k i

theorem zRetraction_degree (n : ℕ) : PathGradedMatrices.Homogeneous
    (fun k=>(k.val.val:ℤ)) (fun i=>(weight i:ℤ)) (zRetraction n) :=
  inverse_degree weight (fun k : Verification.PathCokernel.Weight false (n+1)=>k.val.val) _ _ _ (zProjection_weight n) (zBasis_weight n)

theorem yRetraction_degree (a : ℕ) : PathGradedMatrices.Homogeneous
    (fun k=>(k.val.val:ℤ)) (fun i=>(weight i:ℤ)) (yRetraction a) :=
  inverse_degree weight (fun k : Verification.PathCokernel.Weight true (2*a)=>k.val.val) _ _ _ (yProjection_weight a) (yBasis_weight a)

theorem z_inclusion_retraction (n : ℕ) : zInclusion n*zRetraction n=zProjection n :=
  inclusion_inverse _ _ _ (zInclusion_map n) (zProjection_map n)

theorem y_inclusion_retraction (a : ℕ) : yInclusion a*yRetraction a=yProjection a :=
  inclusion_inverse _ _ _ (yInclusion_map a) (yProjection_map a)

theorem z_retraction_inclusion (n : ℕ) : zRetraction n*zInclusion n=1 :=
  inverse_inclusion _ _ _ (zInclusion_map n)

theorem y_retraction_inclusion (a : ℕ) : yRetraction a*yInclusion a=1 :=
  inverse_inclusion _ _ _ (yInclusion_map a)

#print axioms zProjection_map
#print axioms yProjection_map
#print axioms zProjection_square
#print axioms yProjection_square
#print axioms zInclusion
#print axioms yInclusion
#print axioms zRetraction
#print axioms yRetraction
#print axioms zInclusion_map
#print axioms yInclusion_map
#print axioms zInclusion_degree
#print axioms yInclusion_degree
#print axioms zRetraction_degree
#print axioms yRetraction_degree
#print axioms z_inclusion_retraction
#print axioms y_inclusion_retraction
#print axioms z_retraction_inclusion
#print axioms y_retraction_inclusion

end Verification.PathSurvivorMatrices
