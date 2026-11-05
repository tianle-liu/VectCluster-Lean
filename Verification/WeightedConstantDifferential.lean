/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.WeightedWordComponents

/-!
# Weighted Constant Differential

The complete differential in full word coordinates: positive entries
are the graded coefficient action, and every constant row and column is zero.
-/
noncomputable section
set_option quotPrecheck false
namespace Verification.WeightedConstantDifferential
open Classical CategoryTheory CategoryTheory.Limits
open Verification.WeightedConstantTerms Verification.WeightedConstantCoordinates
open Verification.WeightedWordComponents Verification.GradedCoefficientRealization
variable {C : Type*} [Category C] [Preadditive C] [HasFiniteBiproducts C]
  [HasBinaryBiproducts C] [HasZeroObject C]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι → ℕ) (d : ι → ℤ)
variable (Z : C) (K : ℕ → C)
variable {κ : Type} [Fintype κ] [DecidableEq κ] {v : κ → ℕ}
variable (A : PathGradedCoefficientAction.Action (fun j=>K (j+1)))
variable (T : PositiveGradedContraction.Data w v d)
variable (z : ι) (hz : w z=0) (hd : d z=0) (hu : ∀ i,w i=0 → i=z)
local notation "E" => realizationIso w d Z K z hz hd hu A T
local notation "P" => source K A T
local notation "F" => withConstant K A T Z

theorem zero_source (p q : ℤ) (i : {i // d i=p}) (hi : w i.val=0) :
    biproduct.ι (family w d Z K p) i ≫ (E p).hom ≫ (F).d p q ≫ (E q).inv=0 := by
  have h := congrArg (fun f => biproduct.ι (family w d Z K p) i ≫ f)
    (WeightedConstantCoordinates.differential w d Z K A T z hz hd hu p q)
  calc
    _ = _ := h
    _ = 0 := by
      dsimp only
      rw [←Category.assoc,projection_zero w d Z K A T p i hi,zero_comp]

theorem zero_target (p q : ℤ) (j : {j // d j=q}) (hj : w j.val=0) :
    (E p).hom ≫ (F).d p q ≫ (E q).inv ≫ biproduct.π (family w d Z K q) j=0 := by
  have h := congrArg (fun f => f ≫ biproduct.π (family w d Z K q) j)
    (WeightedConstantCoordinates.differential w d Z K A T z hz hd hu p q)
  simpa only [Category.assoc,inclusion_zero w d Z K A T q j hj,comp_zero] using h

theorem positive (p q : ℤ) (hpq : p+1=q) (i : sourceIndex w d p) (j : sourceIndex w d q) :
    eqToHom (show K (w i.val.val)=family w d Z K p ⟨i.val.val,i.property⟩ from
      (if_neg (Nat.ne_of_gt i.val.property)).symm) ≫
      biproduct.ι (family w d Z K p) ⟨i.val.val,i.property⟩ ≫ (E p).hom ≫ (F).d p q ≫
        (E q).inv ≫ biproduct.π (family w d Z K q) ⟨j.val.val,j.property⟩ ≫
          eqToHom (show family w d Z K q ⟨j.val.val,j.property⟩=K (w j.val.val) from
            if_neg (Nat.ne_of_gt j.val.property))=
      GradedRealizationComponents.entry K A T i.val j.val := by
  have h := congrArg (fun f =>
    eqToHom (show K (w i.val.val)=family w d Z K p ⟨i.val.val,i.property⟩ from
      (if_neg (Nat.ne_of_gt i.val.property)).symm) ≫
      biproduct.ι (family w d Z K p) ⟨i.val.val,i.property⟩ ≫ f ≫
        biproduct.π (family w d Z K q) ⟨j.val.val,j.property⟩ ≫
          eqToHom (show family w d Z K q ⟨j.val.val,j.property⟩=K (w j.val.val) from
            if_neg (Nat.ne_of_gt j.val.property)))
    (WeightedConstantCoordinates.differential w d Z K A T z hz hd hu p q)
  have hc := congrArg₂ (fun f g => f ≫ (P).d p q ≫ g)
    (projection_positive w d Z K A T p i) (inclusion_positive w d Z K A T q j)
  calc
    _ = _ := by simpa only [Category.assoc] using h
    _ = _ := by simpa only [Category.assoc] using hc
    _ = _ := GradedRealizationComponents.component K A T p q hpq i j

#print axioms zero_source
#print axioms zero_target
#print axioms positive
end Verification.WeightedConstantDifferential
