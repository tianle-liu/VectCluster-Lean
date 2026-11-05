/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FiniteAlgebraCoproduct
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Finite Algebra Split

Recursive splitting of the actual finite tensor algebra into its
first factor and the remaining factors, including the empty product.
-/
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1200000
open Classical
namespace Verification.FiniteAlgebraSplit
open scoped TensorProduct
local instance finDecidableEq (m : ℕ) : DecidableEq (Fin m) := fun _ _=>Classical.propDecidable _
variable (R : Type*) [CommRing R] {n : ℕ}
variable (S : Fin (n+1) → Type*) [∀ i,CommRing (S i)] [∀ i,Algebra R (S i)]
local notation "Tail" => ⨂[R] i : Fin n,S i.succ
local notation "All" => ⨂[R] i,S i
local notation "Target" => S 0 ⊗[R] Tail

def factor (i : Fin (n+1)) : S i →ₐ[R] Target :=
  Fin.cases Algebra.TensorProduct.includeLeft
    (fun i=>Algebra.TensorProduct.includeRight.comp
      (PiTensorProduct.singleAlgHom (R:=R) (A:=fun j : Fin n=>S j.succ) i)) i

def forward : All →ₐ[R] Target := FiniteAlgebraCoproduct.lift S (factor R S)
def tailMap : Tail →ₐ[R] All :=
  FiniteAlgebraCoproduct.lift (fun i : Fin n=>S i.succ) (fun i=>PiTensorProduct.singleAlgHom i.succ)
def backward : Target →ₐ[R] All :=
  Algebra.TensorProduct.lift (PiTensorProduct.singleAlgHom 0) (tailMap R S) (fun _ _=>Commute.all _ _)

theorem forward_single (i : Fin (n+1)) (x : S i) :
    forward R S (PiTensorProduct.singleAlgHom i x)=factor R S i x :=
  FiniteAlgebraCoproduct.lift_single S (factor R S) i x

theorem tailMap_single (i : Fin n) (x : S i.succ) :
    tailMap R S (PiTensorProduct.singleAlgHom i x)=PiTensorProduct.singleAlgHom i.succ x :=
  FiniteAlgebraCoproduct.lift_single (fun i : Fin n=>S i.succ) _ i x

theorem backward_tmul (x : S 0) (y : Tail) :
    backward R S (x ⊗ₜ[R] y)=PiTensorProduct.singleAlgHom 0 x * tailMap R S y :=
  Algebra.TensorProduct.lift_tmul _ _ _ x y

theorem forward_tailMap : (forward R S).comp (tailMap R S)=Algebra.TensorProduct.includeRight := by
  apply PiTensorProduct.algHom_ext
  intro i
  apply AlgHom.ext
  intro x
  change forward R S (tailMap R S (PiTensorProduct.singleAlgHom i x))=_
  rw [tailMap_single,forward_single]
  rfl

theorem backward_forward : (backward R S).comp (forward R S)=AlgHom.id R All := by
  apply PiTensorProduct.algHom_ext
  intro i
  apply AlgHom.ext
  intro x
  change backward R S (forward R S (PiTensorProduct.singleAlgHom i x))=PiTensorProduct.singleAlgHom i x
  rw [forward_single]
  induction i using Fin.cases with
  | zero =>
    change backward R S (x ⊗ₜ[R] (1:Tail))=_
    rw [backward_tmul,map_one,mul_one]
  | succ i =>
    change backward R S ((1:S 0) ⊗ₜ[R] PiTensorProduct.singleAlgHom i x)=_
    rw [backward_tmul,map_one,one_mul,tailMap_single]

theorem forward_backward : (forward R S).comp (backward R S)=AlgHom.id R Target := by
  apply Algebra.TensorProduct.ext'
  intro x y
  change forward R S (backward R S (x ⊗ₜ[R] y))=x ⊗ₜ[R] y
  rw [backward_tmul,map_mul,forward_single]
  have ht := DFunLike.congr_fun (forward_tailMap R S) y
  change forward R S (tailMap R S y)=Algebra.TensorProduct.includeRight y at ht
  rw [ht]
  change (x ⊗ₜ[R] (1:Tail))*((1:S 0) ⊗ₜ[R] y)=_
  rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]

def equiv : All ≃ₐ[R] Target := AlgEquiv.ofAlgHom (forward R S) (backward R S)
  (forward_backward R S) (backward_forward R S)

def empty (S : Fin 0 → Type*) [∀ i,CommRing (S i)] [∀ i,Algebra R (S i)] :
    (⨂[R] i,S i) ≃ₐ[R] R :=
  AlgEquiv.ofAlgHom (FiniteAlgebraCoproduct.lift S (fun i=>Fin.elim0 i)) (Algebra.ofId R _)
    (by apply AlgHom.ext; intro r; exact AlgHom.commutes _ r)
    (by apply PiTensorProduct.algHom_ext; intro i; exact Fin.elim0 i)

#print axioms finDecidableEq
#print axioms factor
#print axioms forward
#print axioms tailMap
#print axioms backward
#print axioms forward_single
#print axioms tailMap_single
#print axioms backward_tmul
#print axioms forward_tailMap
#print axioms backward_forward
#print axioms forward_backward
#print axioms equiv
#print axioms empty
end Verification.FiniteAlgebraSplit
