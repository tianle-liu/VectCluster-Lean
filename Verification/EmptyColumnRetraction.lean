/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Sum

/-!
# Empty Column Retraction

Transport a literal integer column splitting across an empty extra
partner index. This is the bookkeeping convention of ScalarFrozenGlobal.
-/
noncomputable section
namespace Verification.EmptyColumnRetraction
open Classical
variable {ρ σ : Type*} [Fintype ρ] [Fintype σ]
variable (B : Matrix ρ (σ ⊕ Empty) ℤ)

def cut : Matrix ρ σ ℤ := fun r i=>B r (Sum.inl i)
def coordinates : (σ → ℤ) ≃ₗ[ℤ] ((σ ⊕ Empty) → ℤ) :=
  LinearEquiv.funCongrLeft ℤ ℤ (Equiv.sumEmpty σ Empty)

omit [Fintype ρ] in
theorem action (x : (σ ⊕ Empty) → ℤ) : B.mulVec x=(cut B).mulVec (fun i=>x (Sum.inl i)) := by
  ext r
  simp [Matrix.mulVec,dotProduct,Fintype.sum_sum_type,cut]

variable (L : (ρ → ℤ) →ₗ[ℤ] (σ → ℤ)) (hL : L.comp (cut B).mulVecLin=LinearMap.id)
def retraction : (ρ → ℤ) →ₗ[ℤ] ((σ ⊕ Empty) → ℤ) := (coordinates (σ:=σ)).toLinearMap.comp L

include hL in
omit [Fintype ρ] in
theorem left : (retraction L).comp B.mulVecLin=LinearMap.id := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun hL (fun i=>x (Sum.inl i))
  change L ((cut B).mulVec (fun i=>x (Sum.inl i)))=(fun i=>x (Sum.inl i)) at h
  funext i
  cases i with
  | inl i =>
    change L (B.mulVec x) i=x (Sum.inl i)
    rw [action,h]
  | inr z => exact z.elim

#print axioms cut
#print axioms coordinates
#print axioms action
#print axioms retraction
#print axioms left
end Verification.EmptyColumnRetraction
