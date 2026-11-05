/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictSingleModel

/-!
# Strict Cell Tests

Coefficients of actual strict cells are additive ambient test groups.
The equivalences follow from the proved strict universal property and
ordinary fully faithfulness A -> D(A), not from full faithfulness of J.
-/
noncomputable section
namespace Verification.StrictCellTests
open CategoryTheory CategoryTheory.Limits
open Verification.StrictSingleModel
attribute [local instance] Abelian.hasFiniteBiproducts
universe w
variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w} A]
variable {D : Type*} [Category D] [Preadditive D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable {d : ℤ} {X : D} (P : Cell J d X)

def testAddEquiv (M : A) : (P.term ⟶ M) ≃+
    (X ⟶ J.obj (DerivedCategory.Q.obj (single d M))) :=
  AddEquiv.ofBijective
    ((StrictTriangleHom.comparison J P.comparison (DerivedCategory.Q.obj (single d M))).comp
      (DerivedCategory.singleFunctor A d).mapAddHom)
    (StrictSingleModel.testEquiv P M).bijective

theorem test_natural {M N : A} (g : M ⟶ N) (f : P.term ⟶ M) :
    testAddEquiv J P N (f ≫ g) = testAddEquiv J P M f ≫
      J.map (DerivedCategory.Q.map ((CochainComplex.singleFunctor A d).map g)) := by
  change P.comparison ≫ J.map ((DerivedCategory.singleFunctor A d).map (f ≫ g)) = _
  simp only [Functor.map_comp,Category.assoc]
  rw [← Category.assoc]
  rfl

def homOfIso {U V : A} (e : U ≅ V) (M : A) : (U ⟶ M) ≃+ (V ⟶ M) where
  toFun f := e.inv ≫ f
  invFun f := e.hom ≫ f
  left_inv f := by simp
  right_inv f := by simp
  map_add' f g := by simp only [Preadditive.comp_add]

def biproductHom {ι : Type} [Fintype ι] (Ps : ι → A) (M : A) :
    ((⨁ Ps) ⟶ M) ≃+ (∀ i,Ps i ⟶ M) where
  toFun f i := biproduct.ι Ps i ≫ f
  invFun f := biproduct.desc f
  left_inv f := by apply biproduct.hom_ext'; intro i; simp
  right_inv f := by funext i; simp
  map_add' f g := by funext i; simp only [Preadditive.comp_add,Pi.add_apply]

def biproductTests {ι : Type} [Fintype ι] (Xs : ι → D) (Ps : ∀ i,Cell J d (Xs i)) (M : A) :
    ((⨁ fun i => (Ps i).term) ⟶ M) ≃+
      (∀ i,Xs i ⟶ J.obj (DerivedCategory.Q.obj (single d M))) :=
  (biproductHom (fun i => (Ps i).term) M).trans (AddEquiv.piCongrRight (fun i => testAddEquiv J (Ps i) M))

#print axioms testAddEquiv
#print axioms test_natural
#print axioms homOfIso
#print axioms biproductHom
#print axioms biproductTests
end Verification.StrictCellTests
