/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FiniteBiproductPartition
import Verification.GradedCoefficientRealization
import Mathlib.Algebra.Homology.HomologicalComplexBiprod

/-!
# Weighted Constant Terms

Separating the unique weight-zero generator in a degreewise finite
sum yields the genuine constant complex plus its positive-weight terms.
-/
noncomputable section
namespace Verification.WeightedConstantTerms
open Classical CategoryTheory CategoryTheory.Limits
variable {C : Type*} [Category C] [Preadditive C] [HasFiniteBiproducts C]
  [HasBinaryBiproducts C] [HasZeroObject C]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι → ℕ) (d : ι → ℤ)
variable (Z : C) (K : ℕ → C)

def family (p : ℤ) (i : {i // d i=p}) : C := if w i.val=0 then Z else K (w i.val)

def positiveIndex (p : ℤ) :
    {i : {i // d i=p} // ¬w i.val=0} ≃ GradedCoefficientRealization.sourceIndex w d p where
  toFun i := ⟨⟨i.val.val,Nat.pos_of_ne_zero i.property⟩,i.val.property⟩
  invFun i := ⟨⟨i.val.val,i.property⟩,Nat.ne_of_gt i.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def positiveIso (p : ℤ) :
    (⨁ Subtype.restrict (fun i : {i // d i=p} => ¬w i.val=0) (family w d Z K p)) ≅
    ⨁ fun i : GradedCoefficientRealization.sourceIndex w d p => K (w i.val.val) :=
  biproduct.whiskerEquiv (positiveIndex w d p) (fun i => eqToIso (by
    change K (w i.val.val)=(if w i.val.val=0 then Z else K (w i.val.val))
    simp only [i.property,if_false]))

variable (z : ι) (hz : w z=0) (hd : d z=0) (hu : ∀ i,w i=0 → i=z)

def zeroIso (p : ℤ) :
    (⨁ Subtype.restrict (fun i : {i // d i=p} => w i.val=0) (family w d Z K p)) ≅
    ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj Z).X p := by
  by_cases hp : p=0
  · subst p
    letI : Unique {i : {i // d i=0} // w i.val=0} :=
      { default := ⟨⟨z,hd⟩,hz⟩
        uniq := fun i => by apply Subtype.ext;apply Subtype.ext;exact hu i.val.val i.property }
    exact biproductUniqueIso _ ≪≫ eqToIso (by exact if_pos (default : {i : {i // d i=0} // w i.val=0}).property) ≪≫
      (HomologicalComplex.singleObjXSelf _ 0 Z).symm
  · have hi : IsZero (⨁ Subtype.restrict (fun i : {i // d i=p} => w i.val=0) (family w d Z K p)) := by
      apply (IsZero.iff_id_eq_zero _).mpr
      apply biproduct.hom_ext
      intro i
      exact (hp (by rw [← i.val.property,hu i.val.val i.property,hd])).elim
    exact hi.iso (HomologicalComplex.isZero_single_obj_X _ 0 Z p hp)

def split (p : ℤ) :
    (⨁ family w d Z K p) ≅
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj Z).X p ⊞
        (⨁ fun i : GradedCoefficientRealization.sourceIndex w d p => K (w i.val.val)) :=
  FiniteBiproductPartition.split _ (fun i=>w i.val=0) ≪≫
    biprod.mapIso (zeroIso w d Z K z hz hd hu p) (positiveIso w d Z K p)

variable {κ : Type} [Fintype κ] [DecidableEq κ] {v : κ → ℕ}
variable (A : PathGradedCoefficientAction.Action (fun j=>K (j+1)))
variable (T : PositiveGradedContraction.Data w v d)

def realizationIso (p : ℤ) :
    (⨁ family w d Z K p) ≅ (GradedCoefficientRealization.withConstant K A T Z).X p :=
  split w d Z K z hz hd hu p ≪≫
    biprod.mapIso (Iso.refl _) (GradedCoefficientRealization.sourceTermIso K A T p).symm ≪≫
      (HomologicalComplex.biprodXIso _ _ p).symm

#print axioms family
#print axioms positiveIndex
#print axioms positiveIso
#print axioms zeroIso
#print axioms split
#print axioms realizationIso
end Verification.WeightedConstantTerms
