/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.TwoDegreeFixedComplex
import Verification.GradedFixedProjection

/-!
# Two Degree Matrix Support

A degree-one differential supported on a two-degree idempotent can only
map degree -1 to degree zero; its actual degree projections recover all of it.
-/

namespace Verification.TwoDegreeMatrixSupport

open Verification.GradedPerturbation Verification.PerturbedHomologyModel
  Verification.GradedSurvivorBasis Verification.GradedFixedProjection

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]

theorem row_zero (d : ι → ℤ) (P S : Matrix ι ι R) (hd : Homogeneous d 1 S)
    (hPS : P*S=S) (hSP : S*P=S)
    (hP : ∀ i j,d i ≠ -1 → d i ≠ 0 → P i j=0)
    (i j : ι) (hi : d i ≠ 0) : S i j=0 := by
  by_cases hi1 : d i = -1
  · rw [← hSP,Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : d k = -1
    · rw [hd i k (by omega),zero_mul]
    · by_cases hk0 : d k=0
      · rw [hd i k (by omega),zero_mul]
      · rw [hP k j hk hk0,mul_zero]
  · rw [← hPS,Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    rw [hP i k hi1 hi,zero_mul]

theorem column_zero (d : ι → ℤ) (P S : Matrix ι ι R) (hd : Homogeneous d 1 S)
    (hPS : P*S=S) (hSP : S*P=S)
    (hP : ∀ i j,d i ≠ -1 → d i ≠ 0 → P i j=0)
    (i j : ι) (hj : d j ≠ -1) : S i j=0 := by
  by_cases hi : d i=0
  · exact hd i j (by omega)
  · exact row_zero d P S hd hPS hSP hP i j hi

theorem image_degree (d : ι → ℤ) (P S : Matrix ι ι R) (hd : Homogeneous d 1 S)
    (hPS : P*S=S) (hSP : S*P=S)
    (hP : ∀ i j,d i ≠ -1 → d i ≠ 0 → P i j=0) (x : ι → R) :
    S.mulVec x ∈ degreeModule d 0 := by
  intro i hi
  change ∑ j,S i j*x j=0
  apply Finset.sum_eq_zero
  intro j _
  rw [row_zero d P S hd hPS hSP hP i j hi,zero_mul]

theorem source_cut (d : ι → ℤ) (P S : Matrix ι ι R) (hd : Homogeneous d 1 S)
    (hPS : P*S=S) (hSP : S*P=S)
    (hP : ∀ i j,d i ≠ -1 → d i ≠ 0 → P i j=0) :
    S*cut d (-1) P=S := by
  calc
    S*cut d (-1) P=S*P := by
      ext i j
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : d k = -1
      · simp only [cut,if_pos hk]
      · simp only [cut,if_neg hk,column_zero d P S hd hPS hSP hP i k hk,zero_mul]
    _=S := hSP

#print axioms row_zero
#print axioms column_zero
#print axioms image_degree
#print axioms source_cut

end Verification.TwoDegreeMatrixSupport
