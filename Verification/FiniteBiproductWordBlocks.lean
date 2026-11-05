/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FiniteBiproductCoordinateBlocks

/-!
# Finite Biproduct Word Blocks

Exact entry transport through finite dependent word sums and a genuine word-index equivalence.
-/
noncomputable section
namespace Verification.FiniteBiproductWordBlocks
open Classical CategoryTheory CategoryTheory.Limits
variable {C : Type*} [Category C] [Preadditive C] [HasFiniteBiproducts C]
variable {ι κ : Type} [Fintype ι] [Fintype κ] {f : ι → C} {g : κ → C}
variable (e : ι ≃ κ) (w : ∀ i,g (e i) ≅ f i)

theorem inverse_inclusion (i : ι) : biproduct.ι g (e i) ≫ (biproduct.whiskerEquiv e w).inv=
    (w i).hom ≫ biproduct.ι f i := by
  have hh := congrArg (fun h=>(w i).hom ≫ h ≫ (biproduct.whiskerEquiv e w).inv)
    (FiniteBiproductCoordinateBlocks.inclusion e w i)
  simpa only [Category.assoc,Iso.hom_inv_id_assoc,Iso.hom_inv_id,Category.comp_id] using hh.symm

theorem forward_projection (i : ι) : (biproduct.whiskerEquiv e w).hom ≫ biproduct.π g (e i)=
    biproduct.π f i ≫ (w i).inv := by
  have hh := congrArg (fun h=>(biproduct.whiskerEquiv e w).hom ≫ h ≫ (w i).inv)
    (FiniteBiproductCoordinateBlocks.projection e w i)
  simpa only [Category.assoc,Iso.hom_inv_id_assoc,Iso.hom_inv_id,Category.comp_id] using hh.symm

variable (σ : ι → Type) [∀ i,Fintype (σ i)] (a : ∀ i,σ i → C)

theorem sigma_projection (i : ι) (j : σ i) :
    (biproductBiproductIso σ a).hom ≫ biproduct.π (fun x : Σ i,σ i=>a x.1 x.2) ⟨i,j⟩=
    biproduct.π (fun i=>⨁ a i) i ≫ biproduct.π (a i) j := by
  simp only [biproductBiproductIso,biproduct.lift_π]

theorem sigma_inclusion (i : ι) (j : σ i) :
    biproduct.ι (fun x : Σ i,σ i=>a x.1 x.2) ⟨i,j⟩ ≫ (biproductBiproductIso σ a).inv=
    biproduct.ι (a i) j ≫ biproduct.ι (fun i=>⨁ a i) i := by
  apply (cancel_mono (biproductBiproductIso σ a).hom).1
  apply biproduct.hom_ext
  rintro ⟨k,l⟩
  simp only [Category.assoc,Iso.inv_hom_id_assoc,Iso.inv_hom_id,Category.comp_id,sigma_projection]
  by_cases hk : k=i
  · subst k
    by_cases hl : l=j
    · subst l;simp
    · simp [Ne.symm hl]
  · have hs : (⟨i,j⟩ : Σ i,σ i)≠⟨k,l⟩ := fun hh=>hk (congrArg Sigma.fst hh).symm
    simp [hs,Ne.symm hk]

#print axioms inverse_inclusion
#print axioms forward_projection
#print axioms sigma_projection
#print axioms sigma_inclusion
end Verification.FiniteBiproductWordBlocks
