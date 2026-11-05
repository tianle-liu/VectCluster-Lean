/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathForestWeightMultiplicity
import Verification.FiniteBiproductPartition

/-!
# Path Forest Positive Multiplicity

Separation of the unique integer summand from the positive Milnor--Witt
summands, with multiplicities equal to the literal manuscript polynomial.
-/
noncomputable section
namespace Verification.PathForestPositiveMultiplicity
open Classical CategoryTheory CategoryTheory.Limits
open Verification.PathForestWeightPolynomial Verification.PathForestZeroWeight
open Verification.WeightedMilnorWittTensor
attribute [local instance] Abelian.hasFiniteBiproducts
variable {S : Type} [Fintype S] (U : Type) [Fintype U] (m : S→ℕ) (o : S→Bool)

def zeroUnique : Unique {a : Choices U m o // weight U m o a=0} where
  default := ⟨zeroChoice U m o,(weight_zero U m o _).mpr rfl⟩
  uniq a := Subtype.ext ((weight_zero U m o a.val).mp a.property)

abbrev PositiveChoice := {a : Choices U m o // weight U m o a≠0}
def positiveWeight (a : PositiveChoice U m o) : ℕ := weight U m o a.val

theorem positive_value (j : Set.range (positiveWeight U m o)) : 0<j.val := by
  obtain ⟨a,ha⟩ := j.property
  rw [←ha]
  exact Nat.pos_of_ne_zero a.property

def positiveFiber (j : ℕ) (hj : j≠0) :
    {a : PositiveChoice U m o // positiveWeight U m o a=j} ≃
      {a : Choices U m o // weight U m o a=j} where
  toFun a := ⟨a.val.val,a.property⟩
  invFun a := ⟨⟨a.val,by rw [a.property];exact hj⟩,a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem multiplicity (j : ℕ) (hj : j≠0) :
    FiniteMultiplicity.multiplicity (positiveWeight U m o) j=(paperPolynomial U m o).coeff j := by
  rw [←PathForestWeightMultiplicity.coefficient U m o j]
  exact Fintype.card_congr (positiveFiber U m o j hj)

variable {A : Type*} [Category A] [Abelian A] (Z : A) (M : ℤ→A)

def zeroIso : (⨁ fun a : {a : Choices U m o // weight U m o a=0}=>object Z M (weight U m o a.val)) ≅ Z := by
  letI := zeroUnique U m o
  exact biproduct.mapIso (fun a=>eqToIso (by simp [object,a.property])) ≪≫
    biproductUniqueIso (fun _ : {a : Choices U m o // weight U m o a=0}=>Z)

def positiveIso : (⨁ fun a : PositiveChoice U m o=>object Z M (weight U m o a.val)) ≅
    ⨁ fun j : Set.range (positiveWeight U m o)=>
      ⨁ fun _ : Fin ((paperPolynomial U m o).coeff j.val)=>M (j.val:ℤ) :=
  biproduct.mapIso (fun a=>eqToIso (by simp only [object,if_neg a.property,positiveWeight])) ≪≫
    BiproductMultiplicity.groupedIso (positiveWeight U m o) (fun j=>M (j:ℤ)) ≪≫
      biproduct.mapIso (fun j=>biproduct.whiskerEquiv
        (f:=fun _ : Fin (FiniteMultiplicity.multiplicity (positiveWeight U m o) j.val)=>M (j.val:ℤ))
        (g:=fun _ : Fin ((paperPolynomial U m o).coeff j.val)=>M (j.val:ℤ))
        (finCongr (multiplicity U m o j.val (Nat.ne_of_gt (positive_value U m o j)))) (fun _=>Iso.refl _))

def iso : (⨁ fun a : Choices U m o=>object Z M (weight U m o a)) ≅
    Z⊞⨁ fun j : Set.range (positiveWeight U m o)=>
      ⨁ fun _ : Fin ((paperPolynomial U m o).coeff j.val)=>M (j.val:ℤ) :=
  FiniteBiproductPartition.split (fun a=>object Z M (weight U m o a)) (fun a=>weight U m o a=0) ≪≫
    biprod.mapIso (zeroIso U m o Z M) (positiveIso U m o Z M)

#print axioms zeroUnique
#print axioms PositiveChoice
#print axioms positiveWeight
#print axioms positive_value
#print axioms positiveFiber
#print axioms multiplicity
#print axioms zeroIso
#print axioms positiveIso
#print axioms iso
end Verification.PathForestPositiveMultiplicity
