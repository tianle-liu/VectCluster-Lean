/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathWordCoefficientGrading
import Verification.PathLiteralEntries
import Verification.PathGradedMatrices
import Verification.PathWeightFiltration

/-!
# Path Matrix Coefficient Grading

Every entry of the literal full-rho path chain differential is homogeneous
of target MW weight minus source MW weight in the actual universal coefficient
ring. This includes the constant-endpoint projections in every stratum.
-/

namespace Verification.PathMatrixCoefficientGrading

open Classical Verification.PathCoefficientRing Verification.PathCoefficientGrading
  Verification.PathWordCoefficientGrading Verification.PathLiteralEntries
  Verification.PathEndpointComplex Verification.PathEndpointWords Verification.PathNormalizedBasis
  Verification.PathEndpointCoordinates Verification.PathCochains Verification.PathRhoConfiguration
  Verification.PathWeightFiltration

theorem power (r : Coeff) (k : ℤ) (hr : PathCoefficientGrading.Homogeneous k r) (n : ℕ) :
    PathCoefficientGrading.Homogeneous ((n:ℤ)*k) (r^n) := by
  induction n with
  | zero => simpa only [pow_zero,Int.natCast_zero,zero_mul] using homogeneous_one
  | succ n ih =>
    convert homogeneous_mul ih hr using 1
    · push_cast
      ring
    · rw [pow_succ]

theorem endpoint_degree (n : ℕ) : PathCoefficientGrading.Homogeneous 1 (endpointConstant rho n) := by
  unfold endpointConstant
  split
  · exact homogeneous_zero _
  · exact homogeneous_rho

theorem projected_column (n i : ℕ) (w : List Bool) :
    ∃ c : Coeff,∃ v : List Bool,projectedFace g rho n i w=c • Finsupp.single v 1 ∧
      PathCoefficientGrading.Homogeneous ((w.count true:ℤ)-v.count true-1) c := by
  obtain ⟨c,v,hc,hcdeg⟩ := face_column (-g) rho (homogeneous_neg homogeneous_g) homogeneous_rho i w
  refine ⟨c*rightScalar (endpointConstant rho n) v,normalizeRight v,?_,?_⟩
  · rw [projectedFace,hc,map_smul,right_projection_column,smul_smul]
  · have hh := homogeneous_mul hcdeg (right_scalar _ (endpoint_degree n) v)
    convert hh using 1
    omega

theorem both_column (a i : ℕ) (w : List Bool) :
    ∃ c : Coeff,∃ v : List Bool,
      Verification.PathLeftEndpoint.projection 0 (projectedFace g rho (2*a) i w)=c • Finsupp.single v 1 ∧
      PathCoefficientGrading.Homogeneous ((w.count true:ℤ)-v.count true-1) c := by
  obtain ⟨c,v,hc,hcdeg⟩ := projected_column (2*a) i w
  refine ⟨c*leftScalar 0 v,normalizeLeft v,?_,?_⟩
  · rw [hc,map_smul,left_projection_column,smul_smul]
  · have hh := homogeneous_mul hcdeg (left_scalar _ (homogeneous_zero _) v)
    convert hh using 1
    omega

theorem single_degree (s : ℤ) (c : Coeff) (v u : List Bool)
    (hc : PathCoefficientGrading.Homogeneous (s-v.count true) c) :
    PathCoefficientGrading.Homogeneous (s-u.count true) ((c • Finsupp.single v 1) u) := by
  by_cases hv : v=u
  · subst u
    simpa only [Finsupp.smul_apply,Finsupp.single_eq_same,smul_eq_mul,mul_one] using hc
  · simpa only [Finsupp.smul_apply,Finsupp.single_eq_of_ne hv,smul_eq_mul,mul_zero]
      using homogeneous_zero (s-u.count true)

theorem z_entry_degree (n : ℕ) (y x : NormalIndex RightNormal n) :
    PathCoefficientGrading.Homogeneous ((weight x:ℤ)-weight y) (zMatrix g rho n y x) := by
  rw [z_entry]
  apply homogeneous_sum
  intro j hj
  by_cases he : eraseConfig y.1 j=x.1
  · rw [if_pos he]
    obtain ⟨c,v,hc,hcdeg⟩ := projected_column n (Verification.PathCompression.faceIndex (eraseConfig y.1 j).val j) x.2.val
    rw [hc]
    have hg := power g 0 homogeneous_g (rank (eraseConfig y.1 j).val j)
    simp only [mul_zero] at hg
    have hh := homogeneous_mul hg (single_degree ((x.2.val.count true:ℤ)-1) c v y.2.val
      (by convert hcdeg using 1; omega))
    have hcard : x.1.val.card+1=y.1.val.card := by
      rw [← he]
      exact Finset.card_erase_add_one hj
    convert hh using 1
    change ((x.1.val.card+x.2.val.count true:ℕ):ℤ)-((y.1.val.card+y.2.val.count true:ℕ):ℤ)=_
    push_cast
    omega
  · rw [if_neg he]
    exact homogeneous_zero _

theorem y_entry_degree (a : ℕ) (y x : NormalIndex BothNormal (2*a)) :
    PathCoefficientGrading.Homogeneous ((weight x:ℤ)-weight y) (yMatrix g rho a y x) := by
  rw [y_entry]
  apply homogeneous_sum
  intro j hj
  by_cases he : eraseConfig y.1 j=x.1
  · rw [if_pos he]
    obtain ⟨c,v,hc,hcdeg⟩ := both_column a (Verification.PathCompression.faceIndex (eraseConfig y.1 j).val j) x.2.val
    rw [hc]
    have hg := power g 0 homogeneous_g (rank (eraseConfig y.1 j).val j)
    simp only [mul_zero] at hg
    have hh := homogeneous_mul hg (single_degree ((x.2.val.count true:ℤ)-1) c v y.2.val
      (by convert hcdeg using 1; omega))
    have hcard : x.1.val.card+1=y.1.val.card := by
      rw [← he]
      exact Finset.card_erase_add_one hj
    convert hh using 1
    change ((x.1.val.card+x.2.val.count true:ℕ):ℤ)-((y.1.val.card+y.2.val.count true:ℕ):ℤ)=_
    push_cast
    omega
  · rw [if_neg he]
    exact homogeneous_zero _

theorem z_chain_degree (n : ℕ) : PathGradedMatrices.Homogeneous (fun i=>(weight i:ℤ))
    (fun i=>(weight i:ℤ)) (zMatrix g rho n).transpose := fun i j=>z_entry_degree n j i

theorem y_chain_degree (a : ℕ) : PathGradedMatrices.Homogeneous (fun i=>(weight i:ℤ))
    (fun i=>(weight i:ℤ)) (yMatrix g rho a).transpose := fun i j=>y_entry_degree a j i

#print axioms power
#print axioms endpoint_degree
#print axioms projected_column
#print axioms both_column
#print axioms single_degree
#print axioms z_entry_degree
#print axioms y_entry_degree
#print axioms z_chain_degree
#print axioms y_chain_degree

end Verification.PathMatrixCoefficientGrading
