/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FiniteAlgebraCoproduct

/-!
# Finite Algebra Reindex

Reindexing the actual finite tensor algebra, with its universal factor maps.
-/
noncomputable section
namespace Verification.FiniteAlgebraReindex
open Classical
open scoped TensorProduct
variable (R : Type*) [CommRing R]
variable {I K : Type*} [Fintype I] [Fintype K]
variable (S : I→Type*) [∀ i,CommRing (S i)] [∀ i,Algebra R (S i)] (e : K≃I)

def forward : (⨂[R] j,S (e j)) →ₐ[R] (⨂[R] i,S i) :=
  FiniteAlgebraCoproduct.lift (fun j=>S (e j)) (fun j=>PiTensorProduct.singleAlgHom (e j))

def backwardFactor (i : I) : S i →ₐ[R] (⨂[R] j,S (e j)) :=
  (e.apply_symm_apply i) ▸
    (PiTensorProduct.singleAlgHom (R:=R) (A:=fun j=>S (e j)) (e.symm i))

def backward : (⨂[R] i,S i) →ₐ[R] (⨂[R] j,S (e j)) :=
  FiniteAlgebraCoproduct.lift S (backwardFactor R S e)

omit [Fintype I] [Fintype K] in
theorem single_transport (j l : K) (h : j=l) :
    ((congrArg e h) ▸ (PiTensorProduct.singleAlgHom (R:=R) (A:=fun j=>S (e j)) j)) =
      PiTensorProduct.singleAlgHom (R:=R) (A:=fun j=>S (e j)) l := by
  cases h
  rfl

omit [Fintype I] [Fintype K] in
theorem backwardFactor_apply (j : K) (x : S (e j)) :
    backwardFactor R S e (e j) x=PiTensorProduct.singleAlgHom j x := by
  exact DFunLike.congr_fun (single_transport R S e (e.symm (e j)) j (e.symm_apply_apply j)) x

theorem backward_forward : (backward R S e).comp (forward R S e)=AlgHom.id R _ := by
  apply PiTensorProduct.algHom_ext
  intro j
  apply AlgHom.ext
  intro x
  change backward R S e (forward R S e (PiTensorProduct.singleAlgHom j x))=_
  rw [forward,FiniteAlgebraCoproduct.lift_single,backward,FiniteAlgebraCoproduct.lift_single,
    backwardFactor_apply]
  rfl

theorem forward_backward : (forward R S e).comp (backward R S e)=AlgHom.id R _ := by
  apply PiTensorProduct.algHom_ext
  intro i
  obtain ⟨j,rfl⟩ := e.surjective i
  apply AlgHom.ext
  intro x
  change forward R S e (backward R S e (PiTensorProduct.singleAlgHom (e j) x))=_
  rw [backward,FiniteAlgebraCoproduct.lift_single,backwardFactor_apply,
    forward,FiniteAlgebraCoproduct.lift_single]
  rfl

def equiv : (⨂[R] j,S (e j)) ≃ₐ[R] (⨂[R] i,S i) :=
  AlgEquiv.ofAlgHom (forward R S e) (backward R S e) (forward_backward R S e) (backward_forward R S e)

#print axioms forward
#print axioms backwardFactor
#print axioms backward
#print axioms single_transport
#print axioms backwardFactor_apply
#print axioms backward_forward
#print axioms forward_backward
#print axioms equiv
end Verification.FiniteAlgebraReindex
