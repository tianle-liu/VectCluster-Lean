/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FullMatrixSelectedSplit
import Verification.PathOriginalConfigurationIndex

/-!
# Path Original Matrix Splittings

Integral splittings of the literal Y and Z exchange matrices. For Z
of odd length the frozen coordinate supplies the missing endpoint row of
the next even path matrix.
-/
noncomputable section
namespace Verification.PathOriginalMatrixSplittings
open Verification.PathLattice
open scoped BigOperators
variable {κ : Type}

def mutableProjection (n : ℕ) : ((Fin n ⊕ κ) → ℤ) →ₗ[ℤ] (Fin n → ℤ) :=
  LinearMap.funLeft ℤ ℤ Sum.inl

def evenRetraction (m : ℕ) : ((Fin (2*m) ⊕ κ) → ℤ) →ₗ[ℤ] (Fin (2*m) → ℤ) :=
  (evenPathEquiv m).symm.toLinearMap.comp (mutableProjection (2*m))

theorem even_left (m : ℕ) (B : Matrix (Fin (2*m) ⊕ κ) (Fin (2*m)) ℤ)
    (hB : ∀ a i,B (Sum.inl a) i=pathMatrix (2*m) a i) :
    (evenRetraction (κ:=κ) m).comp B.mulVecLin=LinearMap.id := by
  apply LinearMap.ext
  intro x
  have hh : mutableProjection (2*m) (B.mulVec x)=evenPathEquiv m x := by
    funext a
    change (∑ i,B (Sum.inl a) i*x i)=∑ i,pathMatrix (2*m) a i*x i
    simp only [hB]
  change (evenPathEquiv m).symm (mutableProjection (2*m) (B.mulVec x))=x
  rw [hh,LinearEquiv.symm_apply_apply]

def prepend (n : ℕ) : (Fin n → ℤ) →ₗ[ℤ] (Fin (n+1) → ℤ) where
  toFun x := Fin.cases 0 x
  map_add' _ _ := by ext i;refine Fin.cases ?_ (fun k=>?_) i <;> rfl
  map_smul' r x := by ext i;refine Fin.cases ?_ (fun k=>?_) i <;> simp [Pi.smul_apply]

def zRows (n : ℕ) : ((Fin n ⊕ Fin 1) → ℤ) →ₗ[ℤ] (Fin (n+1) → ℤ) where
  toFun x := Fin.cases (x (Sum.inr 0)) (fun i=>x (Sum.inl i))
  map_add' _ _ := by ext i;refine Fin.cases ?_ (fun k=>?_) i <;> rfl
  map_smul' r x := by ext i;refine Fin.cases ?_ (fun k=>?_) i <;> simp [Pi.smul_apply]

theorem z_action (n : ℕ) (x : Fin n → ℤ) :
    zRows n (Matrix.mulVec (fun a i=>PathOriginalZPresentation.matrix n a (Sum.inl i)) x)=
      (pathMatrix (n+1)).mulVec (prepend n x) := by
  funext a
  refine Fin.cases ?_ (fun k=>?_) a
  · change (∑ i,PathOriginalZPresentation.matrix n (Sum.inr 0) (Sum.inl i)*x i)=_
    simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,prepend,LinearMap.coe_mk,
      AddHom.coe_mk,Fin.cases_zero,Fin.cases_succ,mul_zero,zero_add]
    apply Finset.sum_congr rfl
    intro i _
    simp [PathOriginalZPresentation.matrix,pathMatrix,Fin.val_succ]
  · change (∑ i,pathMatrix n k i*x i)=_
    simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,prepend,LinearMap.coe_mk,
      AddHom.coe_mk,Fin.cases_zero,Fin.cases_succ,mul_zero,zero_add]
    apply Finset.sum_congr rfl
    intro i _
    simp [pathMatrix,Fin.val_succ]

def oddAmbientEquiv (m : ℕ) : (Fin (2*m+1+1) → ℤ) ≃ₗ[ℤ] (Fin (2*m+1+1) → ℤ) :=
  Matrix.toLin'OfInv (Matrix.nonsing_inv_mul (pathMatrix (2*m+1+1)) (by
    have he : 2*m+1+1=2*(m+1) := by omega
    rw [he];exact even_path_unimodular (m+1)))
    (Matrix.mul_nonsing_inv (pathMatrix (2*m+1+1)) (by
      have he : 2*m+1+1=2*(m+1) := by omega
      rw [he];exact even_path_unimodular (m+1)))

def oddZRetraction (m : ℕ) : ((Fin (2*m+1) ⊕ Fin 1) → ℤ) →ₗ[ℤ] (Fin (2*m+1) → ℤ) :=
  (LinearMap.funLeft ℤ ℤ Fin.succ).comp ((oddAmbientEquiv m).symm.toLinearMap.comp (zRows (2*m+1)))

theorem odd_z_left (m : ℕ) :
    (oddZRetraction m).comp (Matrix.mulVecLin (fun a i=>PathOriginalZPresentation.matrix (2*m+1) a (Sum.inl i)))=LinearMap.id := by
  apply LinearMap.ext
  intro x
  change (fun i=> (oddAmbientEquiv m).symm (zRows (2*m+1) (_root_.Matrix.mulVec _ x)) i.succ)=x
  rw [z_action]
  change (fun i=>(oddAmbientEquiv m).symm (oddAmbientEquiv m (prepend (2*m+1) x)) i.succ)=x
  rw [LinearEquiv.symm_apply_apply]
  rfl

#print axioms mutableProjection
#print axioms evenRetraction
#print axioms even_left
#print axioms prepend
#print axioms zRows
#print axioms z_action
#print axioms oddAmbientEquiv
#print axioms oddZRetraction
#print axioms odd_z_left
end Verification.PathOriginalMatrixSplittings
