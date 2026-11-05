/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Prod
import Verification.PositiveMilnorWittTensorInput
import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Weighted Milnor Witt Tensor

Tensor multiplication of the actual zero-weight integer object and
positive Milnor--Witt objects. The zero-weight normalization identifies the
constant integer sheaf with the ordinary tensor unit; the sole positive input
is the uniform sheaf tensor formula. Distribution over finite sums is proved
using the actual additive monoidal functors.
-/
noncomputable section
namespace Verification.WeightedMilnorWittTensor
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
variable {A : Type*} [Category A] [MonoidalCategory A]
variable (Z : A) (M : ℤ→A)

def object (n : ℕ) : A := if n=0 then Z else M n
variable (unit : Z≅𝟙_ A) (MW : PositiveMilnorWittTensorInput.Standard M)

def multiply : ∀ p q : ℕ,(object Z M p⊗object Z M q)≅object Z M (p+q)
  | 0,q=>by
    simpa only [object,if_pos rfl,Nat.zero_add] using
      (tensorIso unit (Iso.refl (object Z M q)) ≪≫ λ_ (object Z M q))
  | p+1,0=>by
    simpa only [object,Nat.add_zero,if_pos rfl,if_neg (Nat.succ_ne_zero p)] using
      (tensorIso (Iso.refl (M (p+1))) unit ≪≫ ρ_ (M (p+1)))
  | p+1,q+1=>by
    simpa only [object,if_neg (Nat.succ_ne_zero p),if_neg (Nat.succ_ne_zero q),
      if_neg (show p+1+(q+1)≠0 by omega)] using MW.positive (p+1) (q+1) (by omega) (by omega)

variable [Preadditive A] [MonoidalPreadditive A] [HasFiniteBiproducts A]
variable {I K : Type} [Fintype I] [Fintype K] (p : I→ℕ) (q : K→ℕ)

def distribute : ((⨁ fun i=>object Z M (p i))⊗(⨁ fun j=>object Z M (q j))) ≅
    ⨁ fun a : I×K=>object Z M (p a.1+q a.2) :=
  rightDistributor (fun i=>object Z M (p i)) (⨁ fun j=>object Z M (q j)) ≪≫
    biproduct.mapIso (fun i=>leftDistributor (object Z M (p i)) (fun j=>object Z M (q j)) ≪≫
      biproduct.mapIso (fun j=>multiply Z M unit MW (p i) (q j))) ≪≫
    biproductBiproductIso (fun _ : I=>K) (fun i j=>object Z M (p i+q j)) ≪≫
    biproduct.whiskerEquiv (f:=fun a : Sigma (fun _ : I=>K)=>object Z M (p a.1+q a.2))
      (g:=fun a : I×K=>object Z M (p a.1+q a.2))
      (Equiv.sigmaEquivProd I K) (fun _=>Iso.refl _)

#print axioms object
#print axioms multiply
#print axioms distribute
end Verification.WeightedMilnorWittTensor
