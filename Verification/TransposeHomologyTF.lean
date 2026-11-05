/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GradedIntegralSplitting
import Verification.GradedHomologyTF
import Mathlib.Algebra.EuclideanDomain.Int

/-!
# Transpose Homology TF

Integral duality of TF for a finite differential matrix, proved from the
constructed integral splitting rather than assumed as universal coefficients.
-/

namespace Verification.TransposeHomologyTF

open Verification.GradedHomologyTF

variable {R M : Type*} [CommRing R] [IsDomain R]
  [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M]

omit [IsDomain R] in
/-- An integral generalized inverse makes the actual image saturated. -/
theorem total_tf_of_regular (D H : Module.End R M) (h : D.comp (H.comp D)=D) :
    NoZeroSMulDivisors R (Verification.IntegralSplitting.Homology D) := by
  apply (quotient_tf_iff (Verification.IntegralSplitting.boundaryCycles D)).mpr
  intro a ha x hx
  obtain ⟨y,hy⟩ := hx
  have hy' : D y=a • x.val := hy
  have hreg : D (H (D y))=D y := LinearMap.congr_fun h y
  rw [hy',map_smul,map_smul] at hreg
  have hz : a • (D (H x.val)-x.val)=0 := by rw [smul_sub,hreg,sub_self]
  have he : D (H x.val)=x.val :=
    sub_eq_zero.mp ((eq_zero_or_eq_zero_of_smul_eq_zero hz).resolve_left ha)
  exact ⟨H x.val,he⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Chain TF supplies an actual integral contraction; transposition then proves
TF for the actual dual coboundary matrix. -/
theorem transpose_total_tf (D : Matrix ι ι ℤ) (hD : D*D=0)
    (htf : NoZeroSMulDivisors ℤ
      (Verification.IntegralSplitting.Homology (Matrix.toLin' D))) :
    NoZeroSMulDivisors ℤ
      (Verification.IntegralSplitting.Homology (Matrix.toLin' D.transpose)) := by
  letI := htf
  let H := Verification.GradedIntegralSplitting.rawContraction D hD
  have hh : D.transpose*H.transpose*D.transpose=D.transpose := by
    have h := congrArg Matrix.transpose (Verification.GradedIntegralSplitting.raw_generalized D hD)
    simpa only [Matrix.transpose_mul,mul_assoc] using h
  apply total_tf_of_regular (Matrix.toLin' D.transpose) (Matrix.toLin' H.transpose)
  rw [←Matrix.toLin'_mul,←Matrix.toLin'_mul,←mul_assoc,hh]

#print axioms total_tf_of_regular
#print axioms transpose_total_tf

end Verification.TransposeHomologyTF
