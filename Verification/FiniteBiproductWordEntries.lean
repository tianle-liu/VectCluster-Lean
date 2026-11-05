/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FiniteBiproductWordBlocks
import Mathlib.Data.Fintype.Sigma

/-!
# Finite Biproduct Word Entries

Literal block entries after flattening dependent finite word families and reindexing their true biproduct coordinate objects.
-/
noncomputable section
namespace Verification.FiniteBiproductWordEntries
open Classical CategoryTheory CategoryTheory.Limits
variable {C : Type*} [Category C] [Preadditive C] [HasFiniteBiproducts C]
variable {ι κ μ ν : Type} [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ν]
variable (σ : ι → Type) [∀ i,Fintype (σ i)] (a : ∀ i,σ i → C)
variable (b : κ → C) (e : (Σ i,σ i) ≃ κ) (w : ∀ x,b (e x) ≅ a x.1 x.2)

def wordIso : (⨁ fun i=>⨁ a i) ≅ (⨁ b) := biproductBiproductIso σ a ≪≫ biproduct.whiskerEquiv e w

theorem inclusion (i : ι) (j : σ i) :
    biproduct.ι b (e ⟨i,j⟩) ≫ (wordIso σ a b e w).inv=
    (w ⟨i,j⟩).hom ≫ biproduct.ι (a i) j ≫ biproduct.ι (fun i=>⨁ a i) i := by
  rw [wordIso,Iso.trans_inv,←Category.assoc,FiniteBiproductWordBlocks.inverse_inclusion,Category.assoc,
    FiniteBiproductWordBlocks.sigma_inclusion]

theorem projection (i : ι) (j : σ i) :
    (wordIso σ a b e w).hom ≫ biproduct.π b (e ⟨i,j⟩)=
    biproduct.π (fun i=>⨁ a i) i ≫ biproduct.π (a i) j ≫ (w ⟨i,j⟩).inv := by
  rw [wordIso,Iso.trans_hom,Category.assoc,FiniteBiproductWordBlocks.forward_projection,
    ←Category.assoc,FiniteBiproductWordBlocks.sigma_projection,Category.assoc]

variable (τ : μ → Type) [∀ i,Fintype (τ i)] (c : ∀ i,τ i → C)
variable (f : ν → C) (e' : (Σ i,τ i) ≃ ν) (w' : ∀ x,f (e' x) ≅ c x.1 x.2)

theorem entry (d : (⨁ fun i=>⨁ a i) ⟶ (⨁ fun i=>⨁ c i))
    (i : ι) (j : σ i) (k : μ) (l : τ k) :
    biproduct.ι b (e ⟨i,j⟩) ≫ (wordIso σ a b e w).inv ≫ d ≫
      (wordIso τ c f e' w').hom ≫ biproduct.π f (e' ⟨k,l⟩)=
    (w ⟨i,j⟩).hom ≫ (biproduct.ι (a i) j ≫
      (biproduct.ι (fun i=>⨁ a i) i ≫ d ≫ biproduct.π (fun i=>⨁ c i) k) ≫
      biproduct.π (c k) l) ≫ (w' ⟨k,l⟩).inv := by
  rw [projection]
  rw [←Category.assoc,←Category.assoc,←Category.assoc,inclusion]
  simp only [Category.assoc]

#print axioms wordIso
#print axioms inclusion
#print axioms projection
#print axioms entry
end Verification.FiniteBiproductWordEntries
