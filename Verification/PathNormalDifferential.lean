/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.WeightedConstantDifferential
import Verification.PathNormalTermIso

/-!
# Path Normal Differential

Literal full-word entries of both endpoint path differentials,
including the genuine isolated constant word.
-/
noncomputable section
namespace Verification.PathNormalDifferential
open Classical CategoryTheory CategoryTheory.Limits
open Verification.PathWeightFiltration Verification.PathStratumGrading
open Verification.PathNormalizedBasis Verification.PathEndpointWords
open Verification.GradedCoefficientRealization
variable {C : Type*} [Category C] [Preadditive C] [HasFiniteBiproducts C]
  [HasBinaryBiproducts C] [HasZeroObject C]
variable (Z : C) (K : ℕ → C)
variable (A : PathGradedCoefficientAction.Action (fun j=>K (j+1)))

section Y
variable (a : ℕ)

def y (p q : ℤ) :
    (⨁ fun i : {i : NormalIndex BothNormal (2*a) // -degree i=p} => if weight i.val=0 then Z else K (weight i.val)) ⟶
    (⨁ fun j : {j : NormalIndex BothNormal (2*a) // -degree j=q} => if weight j.val=0 then Z else K (weight j.val)) :=
  (PathNormalTermIso.y Z K A a p).hom ≫ (PathGradedSheafModel.ySource K A Z a).d p q ≫
    (PathNormalTermIso.y Z K A a q).inv

theorem y_zero_source (p q : ℤ) (i : {i : NormalIndex BothNormal (2*a) // -degree i=p})
    (hi : weight i.val=0) :
    biproduct.ι (fun i : {i : NormalIndex BothNormal (2*a) // -degree i=p} =>
      if weight i.val=0 then Z else K (weight i.val)) i ≫ y Z K A a p q=0 :=
  WeightedConstantDifferential.zero_source weight (fun i=>-degree i) Z K A (PathPositiveContraction.yData a)
    (PathZeroWeightIndex.yIndex a) (PathZeroWeightIndex.yIndex_weight a)
    (PathZeroWeightIndex.yIndex_degree a) (PathZeroWeightIndex.y_unique a) p q i hi

theorem y_zero_target (p q : ℤ) (j : {j : NormalIndex BothNormal (2*a) // -degree j=q})
    (hj : weight j.val=0) :
    y Z K A a p q ≫ biproduct.π (fun j : {j : NormalIndex BothNormal (2*a) // -degree j=q} =>
      if weight j.val=0 then Z else K (weight j.val)) j=0 := by
  simpa only [y,Category.assoc] using
    WeightedConstantDifferential.zero_target weight (fun i=>-degree i) Z K A (PathPositiveContraction.yData a)
    (PathZeroWeightIndex.yIndex a) (PathZeroWeightIndex.yIndex_weight a)
    (PathZeroWeightIndex.yIndex_degree a) (PathZeroWeightIndex.y_unique a) p q j hj

theorem y_positive (p q : ℤ) (hpq : p+1=q)
    (i : sourceIndex (weight (n:=2*a) (B:=BothNormal)) (fun i=>-degree i) p)
    (j : sourceIndex (weight (n:=2*a) (B:=BothNormal)) (fun i=>-degree i) q) :
    eqToHom (show K (weight i.val.val)=(if weight i.val.val=0 then Z else K (weight i.val.val)) from
      (if_neg (Nat.ne_of_gt i.val.property)).symm) ≫
      biproduct.ι (fun i : {i : NormalIndex BothNormal (2*a) // -degree i=p} =>
        if weight i.val=0 then Z else K (weight i.val)) ⟨i.val.val,i.property⟩ ≫
          y Z K A a p q ≫
      biproduct.π (fun j : {j : NormalIndex BothNormal (2*a) // -degree j=q} =>
        if weight j.val=0 then Z else K (weight j.val)) ⟨j.val.val,j.property⟩ ≫
    eqToHom (show (if weight j.val.val=0 then Z else K (weight j.val.val))=K (weight j.val.val) from
      if_neg (Nat.ne_of_gt j.val.property))=
    GradedRealizationComponents.entry K A (PathPositiveContraction.yData a) i.val j.val := by
  simpa only [y,Category.assoc] using
    WeightedConstantDifferential.positive weight (fun i=>-degree i) Z K A (PathPositiveContraction.yData a)
      (PathZeroWeightIndex.yIndex a) (PathZeroWeightIndex.yIndex_weight a)
      (PathZeroWeightIndex.yIndex_degree a) (PathZeroWeightIndex.y_unique a) p q hpq i j
#print axioms y
#print axioms y_zero_source
#print axioms y_zero_target
#print axioms y_positive
end Y

section Z
variable (n : ℕ)

def z (p q : ℤ) :
    (⨁ fun i : {i : NormalIndex RightNormal (n) // -degree i=p} => if weight i.val=0 then Z else K (weight i.val)) ⟶
    (⨁ fun j : {j : NormalIndex RightNormal (n) // -degree j=q} => if weight j.val=0 then Z else K (weight j.val)) :=
  (PathNormalTermIso.z Z K A n p).hom ≫ (PathGradedSheafModel.zSource K A Z n).d p q ≫
    (PathNormalTermIso.z Z K A n q).inv

theorem z_zero_source (p q : ℤ) (i : {i : NormalIndex RightNormal (n) // -degree i=p})
    (hi : weight i.val=0) :
    biproduct.ι (fun i : {i : NormalIndex RightNormal (n) // -degree i=p} =>
      if weight i.val=0 then Z else K (weight i.val)) i ≫ z Z K A n p q=0 :=
  WeightedConstantDifferential.zero_source weight (fun i=>-degree i) Z K A (PathPositiveContraction.zData n)
    (PathZeroWeightIndex.zIndex n) (PathZeroWeightIndex.zIndex_weight n)
    (PathZeroWeightIndex.zIndex_degree n) (PathZeroWeightIndex.z_unique n) p q i hi

theorem z_zero_target (p q : ℤ) (j : {j : NormalIndex RightNormal (n) // -degree j=q})
    (hj : weight j.val=0) :
    z Z K A n p q ≫ biproduct.π (fun j : {j : NormalIndex RightNormal (n) // -degree j=q} =>
      if weight j.val=0 then Z else K (weight j.val)) j=0 := by
  simpa only [z,Category.assoc] using
    WeightedConstantDifferential.zero_target weight (fun i=>-degree i) Z K A (PathPositiveContraction.zData n)
    (PathZeroWeightIndex.zIndex n) (PathZeroWeightIndex.zIndex_weight n)
    (PathZeroWeightIndex.zIndex_degree n) (PathZeroWeightIndex.z_unique n) p q j hj

theorem z_positive (p q : ℤ) (hpq : p+1=q)
    (i : sourceIndex (weight (n:=n) (B:=RightNormal)) (fun i=>-degree i) p)
    (j : sourceIndex (weight (n:=n) (B:=RightNormal)) (fun i=>-degree i) q) :
    eqToHom (show K (weight i.val.val)=(if weight i.val.val=0 then Z else K (weight i.val.val)) from
      (if_neg (Nat.ne_of_gt i.val.property)).symm) ≫
      biproduct.ι (fun i : {i : NormalIndex RightNormal (n) // -degree i=p} =>
        if weight i.val=0 then Z else K (weight i.val)) ⟨i.val.val,i.property⟩ ≫
          z Z K A n p q ≫
      biproduct.π (fun j : {j : NormalIndex RightNormal (n) // -degree j=q} =>
        if weight j.val=0 then Z else K (weight j.val)) ⟨j.val.val,j.property⟩ ≫
    eqToHom (show (if weight j.val.val=0 then Z else K (weight j.val.val))=K (weight j.val.val) from
      if_neg (Nat.ne_of_gt j.val.property))=
    GradedRealizationComponents.entry K A (PathPositiveContraction.zData n) i.val j.val := by
  simpa only [z,Category.assoc] using
    WeightedConstantDifferential.positive weight (fun i=>-degree i) Z K A (PathPositiveContraction.zData n)
      (PathZeroWeightIndex.zIndex n) (PathZeroWeightIndex.zIndex_weight n)
      (PathZeroWeightIndex.zIndex_degree n) (PathZeroWeightIndex.z_unique n) p q hpq i j
#print axioms z
#print axioms z_zero_source
#print axioms z_zero_target
#print axioms z_positive
end Z
end Verification.PathNormalDifferential
