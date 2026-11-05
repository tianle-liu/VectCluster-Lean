/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib

/-!
# Integer Shear Reflection

Two explicit integral involutions used in the row/column factorization
of ordinary rectangular exchange-matrix mutation.
-/
noncomputable section
namespace Verification.IntegerShearReflection
open Classical
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I] (k : I) (c : I→ℤ)

def rowMap : (I→ℤ)→ₗ[ℤ](I→ℤ) where
  toFun x i := if i=k then -x i else x i+c i*x k
  map_add' x y := by ext i;by_cases h : i=k <;> simp [h] <;> ring
  map_smul' r x := by ext i;by_cases h : i=k <;> simp [h,mul_add,mul_assoc,mul_left_comm]

omit [Fintype I] in
theorem row_involutive : Function.Involutive (rowMap k c) := by
  intro x
  ext i
  by_cases h : i=k <;> simp [rowMap,h]

def row : (I→ℤ)≃ₗ[ℤ](I→ℤ) := LinearEquiv.ofInvolutive (rowMap k c) (row_involutive k c)

def columnMap : (I→ℤ)→ₗ[ℤ](I→ℤ) where
  toFun x i := if i=k then -x k+∑j∈Finset.univ.erase k,c j*x j else x i
  map_add' x y := by
    ext i
    by_cases h : i=k
    · simp [h,mul_add,Finset.sum_add_distrib]
      ring
    · simp [h]
  map_smul' r x := by
    ext i
    change (if i=k then -(r*x k)+∑j∈Finset.univ.erase k,c j*(r*x j) else r*x i)=
      r*(if i=k then -x k+∑j∈Finset.univ.erase k,c j*x j else x i)
    by_cases h : i=k
    · simp only [if_pos h,mul_add,mul_neg,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    · simp only [if_neg h]

theorem column_involutive : Function.Involutive (columnMap k c) := by
  intro x
  ext i
  by_cases h : i=k
  · subst i
    simp only [columnMap,LinearMap.coe_mk,AddHom.coe_mk,ite_true]
    have he : (∑j∈Finset.univ.erase k,c j*(if j=k then -x k+∑l∈Finset.univ.erase k,c l*x l else x j))=
        ∑j∈Finset.univ.erase k,c j*x j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [if_neg (Finset.ne_of_mem_erase hj)]
    rw [he]
    ring
  · simp [columnMap,h]

def column : (I→ℤ)≃ₗ[ℤ](I→ℤ) :=
  LinearEquiv.ofInvolutive (columnMap k c) (column_involutive k c)

theorem column_single (i : I) : column k c (Pi.single i 1)=
    if i=k then -Pi.single k 1 else Pi.single i 1+c i • Pi.single k 1 := by
  ext j
  by_cases hi : i=k <;> by_cases hj : j=k <;>
    simp_all [column,columnMap,Pi.single_apply,eq_comm]


#print axioms rowMap
#print axioms row_involutive
#print axioms row
#print axioms columnMap
#print axioms column_involutive
#print axioms column
#print axioms column_single
end Verification.IntegerShearReflection
