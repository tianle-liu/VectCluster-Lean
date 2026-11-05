/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.IntegerShearReflection
import Verification.FullMatrixSelectedSplit

/-!
# Rectangular Mutation Splitting

Explicit unimodular row and column operations for rectangular exchange
mutation, and internal transport of a full integer splitting.
-/
noncomputable section
namespace Verification.RectangularMutationSplitting
open Classical Verification.IntegerShearReflection
variable {V F : Type} [Fintype V] [Fintype F] [DecidableEq V]
variable (B : Matrix (V⊕F) V ℤ) (k : V)

def rowEquiv : ((V⊕F)→ℤ)≃ₗ[ℤ]((V⊕F)→ℤ) := row (Sum.inl k) (fun a=>max (B a k) 0)
def columnEquiv : (V→ℤ)≃ₗ[ℤ](V→ℤ) := column k (fun i=>max (-B (Sum.inl k) i) 0)
def map : (V→ℤ)→ₗ[ℤ]((V⊕F)→ℤ) :=
  (rowEquiv B k).toLinearMap.comp (B.mulVecLin.comp (columnEquiv B k).toLinearMap)
def matrix : Matrix (V⊕F) V ℤ := LinearMap.toMatrix' (map B k)

omit [Fintype F] in
theorem factorization : (matrix B k).mulVecLin=map B k :=
  Matrix.toLin'_toMatrix' (map B k)

def retraction (r : ((V⊕F)→ℤ)→ₗ[ℤ](V→ℤ)) : ((V⊕F)→ℤ)→ₗ[ℤ](V→ℤ) :=
  (columnEquiv B k).symm.toLinearMap.comp (r.comp (rowEquiv B k).symm.toLinearMap)

omit [Fintype F] in
theorem left (r : ((V⊕F)→ℤ)→ₗ[ℤ](V→ℤ)) (hr : r.comp B.mulVecLin=LinearMap.id) :
    (retraction B k r).comp (matrix B k).mulVecLin=LinearMap.id := by
  rw [factorization]
  apply LinearMap.ext
  intro x
  funext i
  change ((columnEquiv B k).symm
    (r ((rowEquiv B k).symm ((rowEquiv B k) (B.mulVec ((columnEquiv B k) x)))))) i=x i
  rw [LinearEquiv.symm_apply_apply]
  have h := LinearMap.congr_fun hr ((columnEquiv B k) x)
  change r (B.mulVec ((columnEquiv B k) x))=(columnEquiv B k) x at h
  rw [h,LinearEquiv.symm_apply_apply]

theorem selected_AS (r : ((V⊕F)→ℤ)→ₗ[ℤ](V→ℤ)) (hr : r.comp B.mulVecLin=LinearMap.id)
    (I : Finset V) (hzero : ∀i∈I,∀j∈I,matrix B k (Sum.inl i) j=0) :
    AnticliqueSubcolumns.AS (matrix B k) I :=
  FullMatrixSelectedSplit.AS (matrix B k) I (retraction B k r) (left B k r hr) hzero

#print axioms rowEquiv
#print axioms columnEquiv
#print axioms map
#print axioms matrix
#print axioms factorization
#print axioms retraction
#print axioms left
#print axioms selected_AS
end Verification.RectangularMutationSplitting
