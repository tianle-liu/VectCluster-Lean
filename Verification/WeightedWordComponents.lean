/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.WeightedConstantCoordinates
import Verification.GradedRealizationComponents

/-!
# Weighted Word Components

Canonical word entries of the positive projection and inclusion,
including the vanishing of every constant row and column.
-/
noncomputable section
namespace Verification.WeightedWordComponents
open Classical CategoryTheory CategoryTheory.Limits
open Verification.WeightedConstantTerms Verification.WeightedConstantCoordinates
open Verification.GradedCoefficientRealization
variable {C : Type*} [Category C] [Preadditive C] [HasFiniteBiproducts C]
  [HasBinaryBiproducts C] [HasZeroObject C]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι → ℕ) (d : ι → ℤ)
variable (Z : C) (K : ℕ → C)
variable {κ : Type} [Fintype κ] [DecidableEq κ] {v : κ → ℕ}
variable (A : PathGradedCoefficientAction.Action (fun j=>K (j+1)))
variable (T : PositiveGradedContraction.Data w v d)

omit [HasBinaryBiproducts C] [HasZeroObject C] in
theorem projection_zero (p : ℤ) (i : {i // d i=p}) (hi : w i.val=0) :
    biproduct.ι (family w d Z K p) i ≫ projection w d Z K A T p=0 := by
  simp [projection,Category.assoc,biproduct.ι_toSubtype,hi]

omit [HasBinaryBiproducts C] [HasZeroObject C] in
theorem inclusion_zero (p : ℤ) (i : {i // d i=p}) (hi : w i.val=0) :
    inclusion w d Z K A T p ≫ biproduct.π (family w d Z K p) i=0 := by
  simp [inclusion,Category.assoc,biproduct.fromSubtype_π,hi]

omit [HasBinaryBiproducts C] [HasZeroObject C] in
theorem projection_positive (p : ℤ) (i : sourceIndex w d p) :
    eqToHom (show K (w i.val.val)=family w d Z K p ⟨i.val.val,i.property⟩ from
      (if_neg (Nat.ne_of_gt i.val.property)).symm) ≫
      biproduct.ι (family w d Z K p) ⟨i.val.val,i.property⟩ ≫ projection w d Z K A T p=
    biproduct.ι (fun i : sourceIndex w d p=>K (w i.val.val)) i ≫ (sourceTermIso K A T p).inv := by
  simp [projection,Category.assoc,biproduct.ι_toSubtype,Nat.ne_of_gt i.val.property,
    positiveIso,biproduct.whiskerEquiv_hom,positiveIndex]

omit [HasBinaryBiproducts C] [HasZeroObject C] in
theorem inclusion_positive (p : ℤ) (i : sourceIndex w d p) :
    inclusion w d Z K A T p ≫ biproduct.π (family w d Z K p) ⟨i.val.val,i.property⟩ ≫
      eqToHom (show family w d Z K p ⟨i.val.val,i.property⟩=K (w i.val.val) from
        if_neg (Nat.ne_of_gt i.val.property))=
    (sourceTermIso K A T p).hom ≫ biproduct.π (fun i : sourceIndex w d p=>K (w i.val.val)) i := by
  simp only [inclusion,Category.assoc,biproduct.fromSubtype_π,Nat.ne_of_gt i.val.property,
    dite_true]
  rw [positiveIso,biproduct.whiskerEquiv_inv_eq_lift]
  simp [positiveIndex,Category.assoc,Nat.ne_of_gt i.val.property]

#print axioms projection_zero
#print axioms inclusion_zero
#print axioms projection_positive
#print axioms inclusion_positive
end Verification.WeightedWordComponents
