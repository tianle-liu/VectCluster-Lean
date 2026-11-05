/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FiniteSummandHom

/-!
# Finite Summand Boundary Detection

Finitely many representable coefficient tests determine the actual
boundary. Once detected on its target summands, the same matrix acts on
Hom into every coefficient object, without a ring structure on that object.
-/
noncomputable section
namespace Verification.FiniteSummandBoundaryDetection
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [HasFiniteBiproducts C]
variable {ι κ : Type} [Fintype ι] [Fintype κ]
variable (A : ι → C) (B : κ → C)
variable {X Y : C} (e : X ≅ ⨁ A) (f : Y ≅ ⨁ B)

def tests (M : C) : (X ⟶ M) ≃+ (∀ i,A i ⟶ M) :=
  (FiniteSummandHom.precompose M e).trans (FiniteSummandHom.family A M)

def matrixArrow (m : ∀ i j,A i ⟶ B j) : X ⟶ Y :=
  e.hom ≫ biproduct.matrix m ≫ f.inv

theorem matrixArrow_test (m : ∀ i j,A i ⟶ B j) (j : κ) :
    tests A e (B j) (matrixArrow A B e f m ≫ f.hom ≫ biproduct.π B j)=fun i => m i j := by
  funext i
  simp [tests,FiniteSummandHom.precompose,FiniteSummandHom.family,matrixArrow]

theorem detect (d : X ⟶ Y) (m : ∀ i j,A i ⟶ B j)
    (h : ∀ j,tests A e (B j) (d ≫ f.hom ≫ biproduct.π B j)=fun i => m i j) :
    d=matrixArrow A B e f m := by
  apply (cancel_mono f.hom).mp
  apply biproduct.hom_ext
  intro j
  apply (tests A e (B j)).injective
  simpa only [Category.assoc,matrixArrow_test] using h j

def action (m : ∀ i j,A i ⟶ B j) (M : C) : (∀ j,B j ⟶ M) →+ (∀ i,A i ⟶ M) where
  toFun c i := ∑ j,m i j ≫ c j
  map_zero' := by ext i;simp
  map_add' c d := by ext i;simp only [Pi.add_apply,Preadditive.comp_add,Finset.sum_add_distrib]

theorem all_coefficients (d : X ⟶ Y) (m : ∀ i j,A i ⟶ B j)
    (h : ∀ j,tests A e (B j) (d ≫ f.hom ≫ biproduct.π B j)=fun i => m i j)
    (M : C) (c : Y ⟶ M) :
    tests A e M (d ≫ c)=action A B m M (tests B f M c) := by
  rw [detect A B e f d m h]
  funext i
  change biproduct.ι A i ≫ e.inv ≫ (e.hom ≫ biproduct.matrix m ≫ f.inv) ≫ c =
    ∑ j,m i j ≫ (biproduct.ι B j ≫ f.inv ≫ c)
  simp only [Category.assoc,Iso.inv_hom_id_assoc,biproduct.ι_matrix_assoc]
  have hc : f.inv ≫ c=biproduct.desc (fun j => biproduct.ι B j ≫ f.inv ≫ c) := by
    apply biproduct.hom_ext';intro j;simp
  calc
    _ = (biproduct.lift (fun j => m i j)) ≫
        biproduct.desc (fun j => biproduct.ι B j ≫ f.inv ≫ c) :=
      congrArg (fun k => (biproduct.lift (fun j => m i j)) ≫ k) hc
    _ = _ := biproduct.lift_desc

#print axioms tests
#print axioms matrixArrow
#print axioms matrixArrow_test
#print axioms detect
#print axioms action
#print axioms all_coefficients
end Verification.FiniteSummandBoundaryDetection
