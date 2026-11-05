/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.WeightedMilnorWittTensor
import Verification.FiniteContractedProduct
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite Weighted Tensor

The exact finite tensor of weighted Milnor--Witt sums is the finite sum
over all genuine choices, with the sum of their weights. No multiplicity
or cancellation assertion is supplied as an assumption.
-/
noncomputable section
namespace Verification.FiniteWeightedTensor
open Classical CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Verification.WeightedMilnorWittTensor
open scoped BigOperators

variable {n : ℕ} (I : Fin (n+1)→Type)
def choiceEquiv : (I 0×(∀ i : Fin n,I i.succ)) ≃ (∀ i,I i) where
  toFun a := Fin.cases a.1 a.2
  invFun a := (a 0,fun i=>a i.succ)
  left_inv _ := rfl
  right_inv a := by funext i;induction i using Fin.cases <;> rfl

theorem choice_weight (p : ∀ i,I i→ℕ) (a : I 0×(∀ i : Fin n,I i.succ)) :
    ∑ i,p i (choiceEquiv I a i)=p 0 a.1+∑ i : Fin n,p i.succ (a.2 i) := by
  rw [Fin.sum_univ_succ]
  rfl

variable {A : Type*} [Category A] [MonoidalCategory A] [Preadditive A]
variable [MonoidalPreadditive A] [HasFiniteBiproducts A]
variable (Z : A) (M : ℤ→A) (unit : Z≅𝟙_ A) (MW : PositiveMilnorWittTensorInput.Standard M)

def iso : ∀ (n : ℕ) (I : Fin n→Type) [∀ i,Fintype (I i)] (p : ∀ i,I i→ℕ),
    FiniteContractedProduct.survivors Z n (fun i=>⨁ fun a=>object Z M (p i a)) ≅
      ⨁ fun a : ∀ i,I i=>object Z M (∑ i,p i (a i)) := by
  intro n
  induction n with
  | zero=>
    intro I _ p
    exact (biproductUniqueIso (fun a : ∀ i : Fin 0,I i=>object Z M (∑ i,p i (a i))) ≪≫
      eqToIso (by simp [object,FiniteContractedProduct.survivors])).symm
  | succ n ih=>
    intro I _ p
    let tailP := fun a : ∀ i : Fin n,I i.succ=>∑ i : Fin n,p i.succ (a i)
    exact tensorIso (Iso.refl _) (ih (fun i=>I i.succ) (fun i=>p i.succ)) ≪≫
      distribute Z M unit MW (p 0) tailP ≪≫
      biproduct.whiskerEquiv
        (f:=fun a : I 0×(∀ i : Fin n,I i.succ)=>object Z M (p 0 a.1+tailP a.2))
        (g:=fun a : ∀ i : Fin (n+1),I i=>object Z M (∑ i,p i (a i)))
        (choiceEquiv I) (fun a=>eqToIso (congrArg (object Z M) (choice_weight I p a)))

#print axioms choiceEquiv
#print axioms choice_weight
#print axioms iso
end Verification.FiniteWeightedTensor
