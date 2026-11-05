/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathCoefficientGrading
import Mathlib.Data.Matrix.Mul

/-!
# Path Graded Matrices

Actual homogeneous scalar entries are closed under all finite matrix
operations used by the path contraction. Source and target weights may differ;
the coefficient degree is target weight minus source weight.
-/

namespace Verification.PathGradedMatrices

open Verification.PathCoefficientRing Verification.PathCoefficientGrading

variable {ι κ ν : Type*}

def Homogeneous (target : ι → ℤ) (source : κ → ℤ) (M : Matrix ι κ Coeff) : Prop :=
  ∀ i j,PathCoefficientGrading.Homogeneous (target i-source j) (M i j)

theorem zero (target : ι → ℤ) (source : κ → ℤ) :
    Homogeneous target source 0 := fun _ _ => homogeneous_zero _

theorem add (target : ι → ℤ) (source : κ → ℤ) (M N : Matrix ι κ Coeff)
    (hM : Homogeneous target source M) (hN : Homogeneous target source N) :
    Homogeneous target source (M+N) := fun i j => homogeneous_add (hM i j) (hN i j)

theorem neg (target : ι → ℤ) (source : κ → ℤ) (M : Matrix ι κ Coeff)
    (hM : Homogeneous target source M) : Homogeneous target source (-M) :=
  fun i j => homogeneous_neg (hM i j)

theorem sub (target : ι → ℤ) (source : κ → ℤ) (M N : Matrix ι κ Coeff)
    (hM : Homogeneous target source M) (hN : Homogeneous target source N) :
    Homogeneous target source (M-N) := fun i j => homogeneous_sub (hM i j) (hN i j)

theorem one [DecidableEq ι] (weight : ι → ℤ) : Homogeneous weight weight 1 := by
  intro i j
  by_cases h : i=j
  · subst j
    simpa only [Matrix.one_apply_eq,sub_self] using homogeneous_one
  · simpa only [Matrix.one_apply_ne h] using homogeneous_zero (weight i-weight j)

theorem mul [Fintype κ] (target : ι → ℤ) (middle : κ → ℤ) (source : ν → ℤ)
    (M : Matrix ι κ Coeff) (N : Matrix κ ν Coeff)
    (hM : Homogeneous target middle M) (hN : Homogeneous middle source N) :
    Homogeneous target source (M*N) := by
  intro i j
  apply homogeneous_sum
  intro k _
  convert homogeneous_mul (hM i k) (hN k j) using 1
  omega

theorem pow [Fintype ι] [DecidableEq ι] (weight : ι → ℤ)
    (M : Matrix ι ι Coeff) (hM : Homogeneous weight weight M) (n : ℕ) :
    Homogeneous weight weight (M^n) := by
  induction n with
  | zero => simpa only [pow_zero] using one weight
  | succ n ih => simpa only [pow_succ] using mul weight weight weight (M^n) M ih hM

theorem sum {α : Type*} (s : Finset α) (target : ι → ℤ) (source : κ → ℤ)
    (M : α → Matrix ι κ Coeff) (hM : ∀ a∈s,Homogeneous target source (M a)) :
    Homogeneous target source (∑ a∈s,M a) := by
  intro i j
  simp only [Matrix.sum_apply]
  exact homogeneous_sum s _ _ (fun a ha => hM a ha i j)

#print axioms Homogeneous
#print axioms zero
#print axioms add
#print axioms neg
#print axioms sub
#print axioms one
#print axioms mul
#print axioms pow
#print axioms sum

end Verification.PathGradedMatrices
