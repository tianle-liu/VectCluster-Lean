/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictCellTests

/-!
# Strict Cell Iso Transport

The proved strict universal property transports cells along any
ambient isomorphism. The resulting term isomorphism respects all actual
coefficient tests, without choosing coordinate presentations.
-/
noncomputable section
namespace Verification.StrictCellIsoTransport
open CategoryTheory CategoryTheory.Limits
open Verification.StrictSingleModel
universe w
variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w} A]
variable {D : Type*} [Category D] [Preadditive D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable {d : ℤ} {X Y : D} (P : Cell J d X) (Q : Cell J d Y)

def hom (f : X ⟶ Y) : P.term ⟶ Q.term :=
  (StrictCellTests.testAddEquiv J P Q.term).symm (f ≫ Q.comparison)

theorem hom_test (f : X ⟶ Y) (M : A) (a : Q.term ⟶ M) :
    StrictCellTests.testAddEquiv J P M (hom J P Q f ≫ a)=
      f ≫ StrictCellTests.testAddEquiv J Q M a := by
  rw [StrictCellTests.test_natural]
  unfold hom
  rw [AddEquiv.apply_symm_apply]
  simp only [Category.assoc]
  rfl

theorem hom_comp {Z : D} (U : Cell J d Z) (f : X ⟶ Y) (g : Y ⟶ Z) :
    hom J P Q f ≫ hom J Q U g=hom J P U (f ≫ g) := by
  apply (StrictCellTests.testAddEquiv J P U.term).injective
  rw [hom_test]
  simp only [hom,AddEquiv.apply_symm_apply,Category.assoc]

theorem hom_id : hom J P P (𝟙 X)=𝟙 P.term := by
  apply (StrictCellTests.testAddEquiv J P P.term).injective
  simp only [hom,AddEquiv.apply_symm_apply,Category.id_comp]
  change _=P.comparison ≫ J.map ((DerivedCategory.singleFunctor A d).map (𝟙 P.term))
  rw [(DerivedCategory.singleFunctor A d).map_id]
  change P.comparison = P.comparison ≫ J.map (𝟙 (DerivedCategory.Q.obj (single d P.term)))
  rw [J.map_id, Category.comp_id]

def iso (e : X ≅ Y) : P.term ≅ Q.term where
  hom := hom J P Q e.hom
  inv := hom J Q P e.inv
  hom_inv_id := by rw [hom_comp,e.hom_inv_id,hom_id]
  inv_hom_id := by rw [hom_comp,e.inv_hom_id,hom_id]

theorem iso_test (e : X ≅ Y) (M : A) (a : Q.term ⟶ M) :
    StrictCellTests.testAddEquiv J P M ((iso J P Q e).hom ≫ a)=
      e.hom ≫ StrictCellTests.testAddEquiv J Q M a := hom_test J P Q e.hom M a

#print axioms hom
#print axioms hom_test
#print axioms hom_comp
#print axioms hom_id
#print axioms iso
#print axioms iso_test
end Verification.StrictCellIsoTransport
