/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Algebra.Category.Grp.Basic

/-!
# Finite Coefficient Hom

Actual additive maps out of the finite coefficient sum, with the
constant object separate from the positive K_j objects.
-/

noncomputable section
namespace Verification.FiniteCoefficientHom

open CategoryTheory CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
variable {ι : Type} [Fintype ι] (Z M : C) (K : ι → C)

def decomposition : ((Z ⊞ ⨁ K) ⟶ M) ≃+ ((Z ⟶ M) × ((i : ι) → K i ⟶ M)) where
  toFun f := ⟨biprod.inl ≫ f,fun i=>biproduct.ι K i ≫ biprod.inr ≫ f⟩
  invFun f := biprod.desc f.1 (biproduct.desc f.2)
  left_inv f := by
    apply biprod.hom_ext'
    · simp
    · apply biproduct.hom_ext'
      intro i
      simp
  right_inv f := by
    apply Prod.ext
    · simp
    · funext i
      simp
  map_add' f g := by
    apply Prod.ext
    · simp only [Preadditive.comp_add,Prod.fst_add]
    · funext i
      simp only [Preadditive.comp_add,Prod.snd_add,Pi.add_apply]

def decompositionIso : AddCommGrp.of ((Z ⊞ ⨁ K) ⟶ M) ≅
    AddCommGrp.of ((Z ⟶ M) × ((i : ι) → K i ⟶ M)) := (decomposition Z M K).toAddCommGrpIso

/-- Standard representability/contraction identifications can be inserted
one summand at a time; no formula for a path is part of these hypotheses. -/
def contracted (Q₀ : AddCommGrp.{v}) (Q : ι → AddCommGrp.{v})
    (e₀ : (Z ⟶ M) ≃+ Q₀) (e : ∀ i,(K i ⟶ M) ≃+ Q i) :
    AddCommGrp.of ((Z ⊞ ⨁ K) ⟶ M) ≅ AddCommGrp.of (Q₀ × ((i : ι) → Q i)) :=
  ((decomposition Z M K).trans (e₀.prodCongr (AddEquiv.piCongrRight e))).toAddCommGrpIso

#print axioms decomposition
#print axioms decompositionIso
#print axioms contracted

end Verification.FiniteCoefficientHom
