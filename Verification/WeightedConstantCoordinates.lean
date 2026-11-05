/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ConstantBiprodDifferential

/-!
# Weighted Constant Coordinates

The explicit positive projection and inclusion under the unique
constant-word splitting; these retain the canonical word coordinates.
-/
noncomputable section
set_option quotPrecheck false
namespace Verification.WeightedConstantCoordinates
open Classical CategoryTheory CategoryTheory.Limits
open Verification.WeightedConstantTerms
variable {C : Type*} [Category C] [Preadditive C] [HasFiniteBiproducts C]
  [HasBinaryBiproducts C] [HasZeroObject C]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι → ℕ) (d : ι → ℤ)
variable (Z : C) (K : ℕ → C)
variable {κ : Type} [Fintype κ] [DecidableEq κ] {v : κ → ℕ}
variable (A : PathGradedCoefficientAction.Action (fun j=>K (j+1)))
variable (T : PositiveGradedContraction.Data w v d)

def projection (p : ℤ) : (⨁ family w d Z K p) ⟶ (GradedCoefficientRealization.source K A T).X p :=
  biproduct.toSubtype _ (fun i=>¬w i.val=0) ≫ (positiveIso w d Z K p).hom ≫
    (GradedCoefficientRealization.sourceTermIso K A T p).inv

def inclusion (p : ℤ) : (GradedCoefficientRealization.source K A T).X p ⟶ (⨁ family w d Z K p) :=
  (GradedCoefficientRealization.sourceTermIso K A T p).hom ≫ (positiveIso w d Z K p).inv ≫
    biproduct.fromSubtype (family w d Z K p) (fun i=>¬w i.val=0)

variable (z : ι) (hz : w z=0) (hd : d z=0) (hu : ∀ i,w i=0 → i=z)
local notation "S" => (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj Z
local notation "P" => GradedCoefficientRealization.source K A T

theorem hom_projection (p : ℤ) :
    (realizationIso w d Z K z hz hd hu A T p).hom ≫ (biprod.snd : S ⊞ P ⟶ P).f p=
    projection w d Z K A T p := by
  have hs : (HomologicalComplex.biprodXIso S P p).inv ≫ (biprod.snd : S ⊞ P ⟶ P).f p=biprod.snd := by
    apply (cancel_epi (HomologicalComplex.biprodXIso S P p).hom).1
    simp only [Iso.hom_inv_id_assoc,HomologicalComplex.biprodXIso_hom_snd]
  simp only [realizationIso,Iso.trans_hom,Iso.symm_hom,Category.assoc,hs]
  simp [split,FiniteBiproductPartition.split,projection,Category.assoc]

theorem inclusion_inv (p : ℤ) :
    (biprod.inr : P ⟶ S ⊞ P).f p ≫ (realizationIso w d Z K z hz hd hu A T p).inv=
    inclusion w d Z K A T p := by
  have hi : (biprod.inr : P ⟶ S ⊞ P).f p ≫ (HomologicalComplex.biprodXIso S P p).hom=biprod.inr := by
    apply (cancel_mono (HomologicalComplex.biprodXIso S P p).inv).1
    simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id,HomologicalComplex.inr_biprodXIso_inv]
  simp only [realizationIso,Iso.trans_inv,Iso.symm_inv,←Category.assoc,hi]
  simp [split,FiniteBiproductPartition.split,inclusion,Category.assoc]

theorem differential (p q : ℤ) :
    (realizationIso w d Z K z hz hd hu A T p).hom ≫
      (GradedCoefficientRealization.withConstant K A T Z).d p q ≫
        (realizationIso w d Z K z hz hd hu A T q).inv=
    projection w d Z K A T p ≫ (P).d p q ≫ inclusion w d Z K A T q := by
  rw [show (GradedCoefficientRealization.withConstant K A T Z).d p q=
    (S ⊞ P).d p q from rfl,ConstantBiprodDifferential.factor]
  simp only [←Category.assoc,hom_projection]
  simp only [Category.assoc,inclusion_inv]

#print axioms projection
#print axioms inclusion
#print axioms hom_projection
#print axioms inclusion_inv
#print axioms differential
end Verification.WeightedConstantCoordinates
