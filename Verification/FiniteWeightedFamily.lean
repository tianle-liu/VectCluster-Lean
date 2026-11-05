/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FiniteWeightedTensor

/-!
# Finite Weighted Family

The exact weighted finite tensor formula is independent of enumeration;
its summands are the actual dependent choices over the original index type.
-/
noncomputable section
namespace Verification.FiniteWeightedFamily
open Classical CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped BigOperators
variable {I K : Type} [Fintype I] [Fintype K]
variable (S : I→Type) [∀ i,Fintype (S i)] (e : K≃I) (w : ∀ i,S i→ℕ)

omit [∀ i,Fintype (S i)] in
theorem reindex_weight (a : ∀ j,S (e j)) :
    ∑ i,w i (Equiv.piCongrLeft S e a i)=∑ j,w (e j) (a j) := by
  have h := e.sum_comp (fun i=>w i (Equiv.piCongrLeft S e a i))
  simp only [Equiv.piCongrLeft_apply_apply] at h
  exact h.symm

variable {A : Type*} [Category A] [MonoidalCategory A] [Preadditive A]
variable [MonoidalPreadditive A] [HasFiniteBiproducts A]
variable (Z : A) (M : ℤ→A) (unit : Z≅𝟙_ A) (MW : PositiveMilnorWittTensorInput.Standard M)
open Verification.WeightedMilnorWittTensor

def iso : FiniteContractedProduct.survivors Z (Fintype.card I)
    (fun j=>⨁ fun a : S ((Fintype.equivFin I).symm j)=>object Z M (w _ a)) ≅
    ⨁ fun a : ∀ i,S i=>object Z M (∑i,w i (a i)) :=
  FiniteWeightedTensor.iso Z M unit MW (Fintype.card I)
    (fun j=>S ((Fintype.equivFin I).symm j)) (fun j=>w ((Fintype.equivFin I).symm j)) ≪≫
    biproduct.whiskerEquiv
      (f:=fun a : ∀ j : Fin (Fintype.card I),S ((Fintype.equivFin I).symm j)=>
        object Z M (∑j,w ((Fintype.equivFin I).symm j) (a j)))
      (g:=fun a : ∀ i,S i=>object Z M (∑i,w i (a i)))
      (Equiv.piCongrLeft S (Fintype.equivFin I).symm)
      (fun a=>eqToIso (congrArg (object Z M) (reindex_weight S (Fintype.equivFin I).symm w a)))

#print axioms reindex_weight
#print axioms iso
end Verification.FiniteWeightedFamily
