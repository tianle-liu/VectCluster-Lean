/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathLattice
import Mathlib.LinearAlgebra.Pi

/-!
# Path Forest Matching

The consecutive unit matching on every component of a finite path
forest, with its actual integral retraction. Arbitrary diagonal vertex
signs preserve the explicit retraction; no rank or splitting is assumed.
-/

noncomputable section
namespace Verification.PathForestMatching

open Verification.PathLattice

def largeIndex (m : ℕ) : Bool → Type
  | false => Fin m
  | true => Fin (m+1)

instance largeFintype (m : ℕ) (o : Bool) : Fintype (largeIndex m o) := by cases o <;> dsimp only [largeIndex] <;> exact inferInstance
instance largeDecidableEq (m : ℕ) (o : Bool) : DecidableEq (largeIndex m o) := by cases o <;> dsimp only [largeIndex] <;> exact inferInstance

def localMatching (m : ℕ) (o : Bool) : (Fin m → ℤ) →ₗ[ℤ] (largeIndex m o → ℤ) :=
  match o with
  | false => (bidiagonal m).mulVecLin
  | true => (difference m).mulVecLin

def localRetraction (m : ℕ) (o : Bool) : (largeIndex m o → ℤ) →ₗ[ℤ] (Fin m → ℤ) :=
  match o with
  | false => (bidiagonalEquiv m).symm.toLinearMap
  | true => differenceRetraction m

theorem local_left (m : ℕ) (o : Bool) : (localRetraction m o).comp (localMatching m o)=LinearMap.id := by
  cases o with
  | false =>
    apply LinearMap.ext
    intro x
    exact (bidiagonalEquiv m).symm_apply_apply x
  | true => exact differenceRetraction_leftInverse m

variable {S : Type} (m : S → ℕ) (o : S → Bool)
abbrev Large := (s : S) → largeIndex (m s) (o s) → ℤ
abbrev Small := (s : S) → Fin (m s) → ℤ

def matching : Small m →ₗ[ℤ] Large m o where
  toFun x s := localMatching (m s) (o s) (x s)
  map_add' _ _ := by funext s;exact map_add _ _ _
  map_smul' a x := by funext s;exact (localMatching (m s) (o s)).map_smul a (x s)

def retraction : Large m o →ₗ[ℤ] Small m where
  toFun x s := localRetraction (m s) (o s) (x s)
  map_add' _ _ := by funext s;exact map_add _ _ _
  map_smul' a x := by funext s;exact (localRetraction (m s) (o s)).map_smul a (x s)

theorem left : (retraction m o).comp (matching m o)=LinearMap.id := by
  apply LinearMap.ext
  intro x
  funext s
  exact LinearMap.congr_fun (local_left (m s) (o s)) (x s)

variable {ι : Type}
/-- Every vertex rescaling is an actual integral coordinate equivalence. -/
def scaling (u : ι → ℤˣ) : (ι → ℤ) ≃ₗ[ℤ] (ι → ℤ) where
  toFun x i := (u i:ℤ)*x i
  invFun x i := ((u i)⁻¹:ℤˣ)*x i
  left_inv x := by funext i;simp [← mul_assoc]
  right_inv x := by funext i;simp [← mul_assoc]
  map_add' x y := by funext i;exact mul_add _ _ _
  map_smul' a x := by funext i;change _*(a*_)=a*(_*_);ring

variable (u : (s : S) → largeIndex (m s) (o s) → ℤˣ) (v : (s : S) → Fin (m s) → ℤˣ)
def largeScaling : Large m o ≃ₗ[ℤ] Large m o := LinearEquiv.piCongrRight (fun s=>scaling (u s))
def smallScaling : Small m ≃ₗ[ℤ] Small m := LinearEquiv.piCongrRight (fun s=>scaling (v s))

def signedMatching : Small m →ₗ[ℤ] Large m o :=
  (largeScaling m o u).toLinearMap.comp ((matching m o).comp (smallScaling m v).toLinearMap)

def signedRetraction : Large m o →ₗ[ℤ] Small m :=
  (smallScaling m v).symm.toLinearMap.comp ((retraction m o).comp (largeScaling m o u).symm.toLinearMap)

theorem signed_left : (signedRetraction m o u v).comp (signedMatching m o u v)=LinearMap.id := by
  apply LinearMap.ext
  intro x
  change (smallScaling m v).symm (retraction m o
    ((largeScaling m o u).symm (largeScaling m o u (matching m o (smallScaling m v x)))))=x
  rw [LinearEquiv.symm_apply_apply]
  have h:=LinearMap.congr_fun (left m o) (smallScaling m v x)
  change retraction m o (matching m o (smallScaling m v x))=smallScaling m v x at h
  rw [h,LinearEquiv.symm_apply_apply]

#print axioms largeIndex
#print axioms largeFintype
#print axioms largeDecidableEq
#print axioms localMatching
#print axioms localRetraction
#print axioms local_left
#print axioms Large
#print axioms Small
#print axioms matching
#print axioms retraction
#print axioms left
#print axioms scaling
#print axioms largeScaling
#print axioms smallScaling
#print axioms signedMatching
#print axioms signedRetraction
#print axioms signed_left

end Verification.PathForestMatching
