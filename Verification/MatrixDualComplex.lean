/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.MatrixDualCoordinates
import Verification.TransposeReduction

/-!
# Matrix Dual Complex

An actual coefficient isomorphism of finite matrix complexes dualizes to
an actual isomorphism of their transposes, with explicitly reversed degree.
-/

namespace Verification.MatrixDualComplex

open CategoryTheory Verification.GradedPerturbation Verification.MatrixDualCoordinates

variable {R ι κ : Type} [CommRing R]
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem dual_intertwining (E : (ι → R) ≃ₗ[R] (κ → R)) (A : Matrix ι ι R) (B : Matrix κ κ R)
    (h : (Matrix.toLin' B).comp E.toLinearMap=E.toLinearMap.comp (Matrix.toLin' A)) :
    (Matrix.toLin' B.transpose).comp (dualEquiv E).toLinearMap=
      (dualEquiv E).toLinearMap.comp (Matrix.toLin' A.transpose) := by
  have hI : E.symm.toLinearMap.comp (Matrix.toLin' B)=
      (Matrix.toLin' A).comp E.symm.toLinearMap := by
    apply LinearMap.ext
    intro x
    have hh := congrArg E.symm (LinearMap.congr_fun h (E.symm x))
    simpa only [LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
      LinearEquiv.apply_symm_apply,LinearEquiv.symm_apply_apply] using hh
  have hm := congrArg LinearMap.toMatrix' hI
  simp only [LinearMap.toMatrix'_comp,LinearMap.toMatrix'_toLin'] at hm
  have ht := congrArg Matrix.transpose hm
  simp only [Matrix.transpose_mul] at ht
  apply LinearMap.ext
  intro x
  change B.transpose.mulVec ((LinearMap.toMatrix' E.symm.toLinearMap).transpose.mulVec x)=
    (LinearMap.toMatrix' E.symm.toLinearMap).transpose.mulVec (A.transpose.mulVec x)
  rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,ht]

noncomputable def complexIso (d : ι → ℤ) (e : κ → ℤ) (E : (ι → R) ≃ₗ[R] (κ → R))
    (hE : ∀ p x,x ∈ degreeModule d p → E x ∈ degreeModule e p)
    (hI : ∀ p x,x ∈ degreeModule e p → E.symm x ∈ degreeModule d p)
    (A : Matrix ι ι R) (B : Matrix κ κ R)
    (hdA : Homogeneous d 1 A) (hdB : Homogeneous e 1 B) (hA : A*A=0) (hB : B*B=0)
    (h : (Matrix.toLin' B).comp E.toLinearMap=E.toLinearMap.comp (Matrix.toLin' A)) :
    matrixComplex (fun i => -d i) A.transpose
      (Verification.TransposeReduction.homogeneous_transpose d 1 A hdA)
      (by rw [← Matrix.transpose_mul,hA,Matrix.transpose_zero]) ≅
    matrixComplex (fun j => -e j) B.transpose
      (Verification.TransposeReduction.homogeneous_transpose e 1 B hdB)
      (by rw [← Matrix.transpose_mul,hB,Matrix.transpose_zero]) :=
  Verification.MatrixDegreeEquivalence.complexIso _ _ (dualEquiv E)
    (dual_degree d e E hI) (dual_inverse_degree d e E hE) _ _ _ _ _ _ (dual_intertwining E A B h)

#print axioms dual_intertwining
#print axioms complexIso

end Verification.MatrixDualComplex
