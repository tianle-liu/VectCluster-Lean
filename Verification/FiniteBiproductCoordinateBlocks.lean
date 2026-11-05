/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Finite Biproduct Coordinate Blocks

Exact block formulas for finite biproduct coordinate isomorphisms, including index equivalences.
-/
noncomputable section
namespace Verification.FiniteBiproductCoordinateBlocks
open Classical CategoryTheory CategoryTheory.Limits
variable {C : Type*} [Category C] [Preadditive C] [HasFiniteBiproducts C]
variable {ι κ μ ν : Type} [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ν]
variable {f : ι → C} {g : κ → C} {h : μ → C} {k : ν → C}
variable (e : ι ≃ κ) (w : ∀ i,g (e i) ≅ f i)

theorem inclusion (i : ι) : biproduct.ι f i ≫ (biproduct.whiskerEquiv e w).hom=
    (w i).inv ≫ biproduct.ι g (e i) := by
  simp only [biproduct.whiskerEquiv,biproduct.ι_desc]

theorem projection (i : ι) : (biproduct.whiskerEquiv e w).inv ≫ biproduct.π f i=
    biproduct.π g (e i) ≫ (w i).hom := by
  apply (cancel_epi (biproduct.whiskerEquiv e w).hom).1
  apply biproduct.hom_ext'
  intro j
  by_cases he : j=i
  · subst j
    simp only [Category.assoc,Iso.hom_inv_id_assoc]
    rw [←Category.assoc,←Category.assoc,inclusion]
    simp only [Category.assoc,biproduct.ι_π_self_assoc,biproduct.ι_π_self,Iso.inv_hom_id,Category.id_comp]
  · have hej : e j≠e i := fun hh=>he (e.injective hh)
    simp only [Category.assoc,Iso.hom_inv_id_assoc]
    rw [biproduct.ι_π_ne _ he]
    rw [←Category.assoc,←Category.assoc,inclusion]
    simp [Category.assoc,hej]

theorem block (e' : μ ≃ ν) (w' : ∀ i,k (e' i) ≅ h i) (d : (⨁ g) ⟶ (⨁ k)) (i : ι) (j : μ) :
    biproduct.ι f i ≫ (biproduct.whiskerEquiv e w).hom ≫ d ≫
      (biproduct.whiskerEquiv e' w').inv ≫ biproduct.π h j=
    (w i).inv ≫ (biproduct.ι g (e i) ≫ d ≫ biproduct.π k (e' j)) ≫ (w' j).hom := by
  rw [projection]
  rw [←Category.assoc,←Category.assoc,inclusion]
  simp only [Category.assoc]

#print axioms inclusion
#print axioms projection
#print axioms block
end Verification.FiniteBiproductCoordinateBlocks
