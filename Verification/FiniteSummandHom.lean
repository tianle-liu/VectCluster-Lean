/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FiniteCoefficientHom
import Mathlib.Data.DFinsupp.Defs

/-!
# Finite Summand Hom

Applying additive Hom to a constructed finite direct-sum equivalence,
with the coefficient groups returned as literal finitely supported families.
-/
noncomputable section
namespace Verification.FiniteSummandHom
open CategoryTheory CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [HasFiniteBiproducts C] [HasBinaryBiproducts C]
variable {ι κ : Type} [Fintype ι] [Fintype κ]
variable (A : ι → C) (B : κ → C) (E : C)

def family : ((⨁ A) ⟶ E) ≃+ (∀ i,A i ⟶ E) where
  toFun f i := biproduct.ι A i ≫ f
  invFun f := biproduct.desc f
  left_inv f := by apply biproduct.hom_ext'; intro i; simp
  right_inv f := by funext i; simp
  map_add' f g := by funext i; simp only [Preadditive.comp_add,Pi.add_apply]

def finiteSupport : (∀ i,A i ⟶ E) ≃+ (Π₀ i,A i ⟶ E) where
  toEquiv := DFinsupp.equivFunOnFintype.symm
  map_add' f g := by ext i; rfl

def bothFamilies : (((⨁ A) ⊞ (⨁ B)) ⟶ E) ≃+
    ((Π₀ i,A i ⟶ E) × (Π₀ k,B k ⟶ E)) :=
  (FiniteCoefficientHom.decomposition (⨁ A) E B).trans
    (((family A E).trans (finiteSupport A E)).prodCongr (finiteSupport B E))

variable {X Y : C}

def precompose (e : X ≅ Y) : (X ⟶ E) ≃+ (Y ⟶ E) where
  toFun f := e.inv ≫ f
  invFun f := e.hom ≫ f
  left_inv f := by simp
  right_inv f := by simp
  map_add' f g := by simp only [Preadditive.comp_add]

def coefficients (e : X ≅ (⨁ A) ⊞ (⨁ B)) : (X ⟶ E) ≃+
    ((Π₀ i,A i ⟶ E) × (Π₀ k,B k ⟶ E)) :=
  (precompose E e).trans (bothFamilies A B E)

#print axioms family
#print axioms finiteSupport
#print axioms bothFamilies
#print axioms precompose
#print axioms coefficients
end Verification.FiniteSummandHom
