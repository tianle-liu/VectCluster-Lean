/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.MatrixDegreeEquivalence

/-!
# Matrix Dual Coordinates

Contragradient coefficient changes for literal transposed finite matrices.
The inverse transpose is constructed explicitly, including its grading.
-/

namespace Verification.MatrixDualCoordinates

open Verification.GradedPerturbation

variable {R ι κ : Type} [CommRing R]
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem matrix_inverse (E : (ι → R) ≃ₗ[R] (κ → R)) :
    LinearMap.toMatrix' E.symm.toLinearMap * LinearMap.toMatrix' E.toLinearMap=1 := by
  rw [← LinearMap.toMatrix'_comp]
  have h : E.symm.toLinearMap.comp E.toLinearMap=LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact E.symm_apply_apply x
  rw [h,LinearMap.toMatrix'_id]

noncomputable def dualEquiv (E : (ι → R) ≃ₗ[R] (κ → R)) : (ι → R) ≃ₗ[R] (κ → R) :=
  { Matrix.toLin' (LinearMap.toMatrix' E.symm.toLinearMap).transpose with
    invFun := (LinearMap.toMatrix' E.toLinearMap).transpose.mulVec
    left_inv := by
      intro x
      change (LinearMap.toMatrix' E.toLinearMap).transpose.mulVec
        ((LinearMap.toMatrix' E.symm.toLinearMap).transpose.mulVec x)=x
      rw [Matrix.mulVec_mulVec,← Matrix.transpose_mul,matrix_inverse,Matrix.transpose_one,Matrix.one_mulVec]
    right_inv := by
      intro x
      change (LinearMap.toMatrix' E.symm.toLinearMap).transpose.mulVec
        ((LinearMap.toMatrix' E.toLinearMap).transpose.mulVec x)=x
      have h := matrix_inverse E.symm
      simp only [LinearEquiv.symm_symm] at h
      rw [Matrix.mulVec_mulVec,← Matrix.transpose_mul,h,Matrix.transpose_one,Matrix.one_mulVec] }

omit [Fintype κ] [DecidableEq κ] in
theorem matrix_entry_degree (d : ι → ℤ) (e : κ → ℤ) (F : (ι → R) →ₗ[R] (κ → R))
    (hF : ∀ p x,x ∈ degreeModule d p → F x ∈ degreeModule e p)
    (j : κ) (i : ι) (hji : e j ≠ d i) : LinearMap.toMatrix' F j i=0 := by
  have hh : Pi.single i (1:R) ∈ degreeModule d (d i) := by
    intro a ha
    exact Pi.single_eq_of_ne (fun he => ha (congrArg d he)) 1
  have he := hF (d i) (Pi.single i 1) hh j hji
  rw [LinearMap.toMatrix'_apply]
  rw [show (fun j : ι => if j=i then (1:R) else 0)=Pi.single i 1 by
    funext j; simp [Pi.single_apply,eq_comm]]
  exact he

omit [DecidableEq κ] in
theorem transpose_degree (d : ι → ℤ) (e : κ → ℤ) (F : (ι → R) →ₗ[R] (κ → R))
    (hF : ∀ p x,x ∈ degreeModule d p → F x ∈ degreeModule e p)
    (p : ℤ) (x : κ → R) (hx : x ∈ degreeModule (fun j => -e j) p) :
    (LinearMap.toMatrix' F).transpose.mulVec x ∈ degreeModule (fun i => -d i) p := by
  intro i hi
  change -d i ≠ p at hi
  change ∑ j,LinearMap.toMatrix' F j i*x j=0
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : -e j=p
  · rw [matrix_entry_degree d e F hF j i (by omega),zero_mul]
  · rw [hx j hj,mul_zero]

theorem dual_degree (d : ι → ℤ) (e : κ → ℤ) (E : (ι → R) ≃ₗ[R] (κ → R))
    (hI : ∀ p x,x ∈ degreeModule e p → E.symm x ∈ degreeModule d p)
    (p : ℤ) (x : ι → R) (hx : x ∈ degreeModule (fun i => -d i) p) :
    dualEquiv E x ∈ degreeModule (fun j => -e j) p :=
  transpose_degree e d E.symm.toLinearMap hI p x hx

theorem dual_inverse_degree (d : ι → ℤ) (e : κ → ℤ) (E : (ι → R) ≃ₗ[R] (κ → R))
    (hE : ∀ p x,x ∈ degreeModule d p → E x ∈ degreeModule e p)
    (p : ℤ) (x : κ → R) (hx : x ∈ degreeModule (fun j => -e j) p) :
    (dualEquiv E).symm x ∈ degreeModule (fun i => -d i) p :=
  transpose_degree d e E.toLinearMap hE p x hx

#print axioms matrix_inverse
#print axioms dualEquiv
#print axioms matrix_entry_degree
#print axioms transpose_degree
#print axioms dual_degree
#print axioms dual_inverse_degree

end Verification.MatrixDualCoordinates
