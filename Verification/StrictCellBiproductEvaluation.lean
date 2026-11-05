/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictCellTests

/-!
# Strict Cell Biproduct Evaluation

Ordinary coefficient tests of the actual finite strict-cell sum agree
with the independently constructed component tests.
-/
noncomputable section
namespace Verification.StrictCellBiproductEvaluation
open CategoryTheory CategoryTheory.Limits
open Verification.StrictSingleModel
attribute [local instance] Abelian.hasFiniteBiproducts
universe w
variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w} A]
variable {D : Type*} [Category D] [Preadditive D] [HasFiniteBiproducts D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable {ι : Type} [Fintype ι] {d : ℤ} (X : ι → D) (P : ∀ i, Cell J d (X i))
variable (M : A)

theorem component (f : (sum X P).term ⟶ M) (i : ι) :
    biproduct.ι X i ≫ StrictCellTests.testAddEquiv J (sum X P) M f =
      StrictCellTests.biproductTests J X P M f i := by
  change biproduct.ι X i ≫ (sum X P).comparison ≫
      J.map (DerivedCategory.Q.map ((CochainComplex.singleFunctor A d).map f)) =
    (P i).comparison ≫ J.map (DerivedCategory.Q.map
      ((CochainComplex.singleFunctor A d).map (biproduct.ι (fun i => (P i).term) i ≫ f)))
  simp only [StrictSingleModel.sum,FiniteStrictModels.comparison,Category.assoc,
    biproduct.ι_desc_assoc,← Functor.map_comp]
  congr 1
  congr 1
  simp only [FiniteStrictModels.inclusion,Functor.mapBiproduct_inv,
    biproduct.ι_desc_assoc,Functor.map_comp]
  simp only [← Functor.map_comp,biproduct.ι_desc_assoc]

theorem assemble (f : (sum X P).term ⟶ M) :
    StrictCellTests.testAddEquiv J (sum X P) M f =
      biproduct.desc (StrictCellTests.biproductTests J X P M f) := by
  apply biproduct.hom_ext'
  intro i
  rw [component,biproduct.ι_desc]

variable {Y : D} (e : Y ≅ ⨁ X)

theorem transported (f : (ofIso (sum X P) e).term ⟶ M) :
    StrictCellTests.testAddEquiv J (ofIso (sum X P) e) M f =
      e.hom ≫ biproduct.desc (StrictCellTests.biproductTests J X P M f) := by
  change (e.hom ≫ (sum X P).comparison) ≫ _ = _
  rw [Category.assoc]
  exact congrArg (fun a => e.hom ≫ a) (assemble J X P M f)

#print axioms component
#print axioms assemble
#print axioms transported
end Verification.StrictCellBiproductEvaluation
