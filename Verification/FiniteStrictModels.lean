/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictProjectiveModel
import Verification.FiniteProjectiveBiproduct

/-!
# Finite Strict Models

A finite family of strict models supplies a strict model of the actual
ambient biproduct. The comparison and its Hom bijection are constructed;
no full faithfulness of the realization functor is assumed.
-/
noncomputable section
namespace Verification.FiniteStrictModels
open CategoryTheory CategoryTheory.Limits
open Verification.StrictTriangleHom Verification.StrictProjectiveModel
attribute [local instance] Abelian.hasFiniteBiproducts
universe w
variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w} A]
variable {D : Type*} [Category D] [Preadditive D] [HasFiniteBiproducts D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable {ι : Type} [Fintype ι] (X : ι → D) (M : ∀ i, Model J (X i))

abbrev complexes : ι → CochainComplex A ℤ := fun i => (M i).complex

def inclusion (i : ι) : DerivedCategory.Q.obj ((M i).complex) ⟶
    DerivedCategory.Q.obj (⨁ complexes J X M) :=
  DerivedCategory.Q.map (biproduct.ι (complexes J X M) i)

def comparison : (⨁ X) ⟶ J.obj (DerivedCategory.Q.obj (⨁ complexes J X M)) :=
  biproduct.desc fun i => (M i).comparison ≫ J.map (inclusion J X M i)

omit [HasFiniteBiproducts D] in
theorem inclusion_ext {E : DerivedCategory A}
    (f g : DerivedCategory.Q.obj (⨁ complexes J X M) ⟶ E)
    (h : ∀ i, inclusion J X M i ≫ f = inclusion J X M i ≫ g) : f = g := by
  apply (cancel_epi (DerivedCategory.Q.mapBiproduct (complexes J X M)).inv).mp
  apply biproduct.hom_ext'
  intro i
  simpa only [Functor.mapBiproduct_inv, ← Category.assoc, biproduct.ι_desc] using h i

def assemble {E : DerivedCategory A} (f : ∀ i, DerivedCategory.Q.obj ((M i).complex) ⟶ E) :
    DerivedCategory.Q.obj (⨁ complexes J X M) ⟶ E :=
  (DerivedCategory.Q.mapBiproduct (complexes J X M)).hom ≫ biproduct.desc f

omit [HasFiniteBiproducts D] in
theorem inclusion_assemble {E : DerivedCategory A}
    (f : ∀ i, DerivedCategory.Q.obj ((M i).complex) ⟶ E) (i : ι) :
    inclusion J X M i ≫ assemble J X M f = f i := by
  have hi : biproduct.ι (fun j => DerivedCategory.Q.obj ((M j).complex)) i ≫
      (DerivedCategory.Q.mapBiproduct (complexes J X M)).inv = inclusion J X M i := by
    simp only [Functor.mapBiproduct_inv, biproduct.ι_desc, inclusion]
  rw [← hi, assemble, Category.assoc, Iso.inv_hom_id_assoc, biproduct.ι_desc]

theorem universal : Universal J (comparison J X M) := by
  intro E
  constructor
  · intro f g h
    apply inclusion_ext J X M f g
    intro i
    apply ((M i).universal E).injective
    have hi := congrArg (fun a => biproduct.ι X i ≫ a) h
    simpa only [StrictTriangleHom.comparison, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      comparison, biproduct.ι_desc_assoc, J.map_comp, Category.assoc] using hi
  · intro u
    choose f hf using fun i => ((M i).universal E).surjective (biproduct.ι X i ≫ u)
    refine ⟨assemble J X M f,?_⟩
    apply biproduct.hom_ext'
    intro i
    change biproduct.ι X i ≫ (comparison J X M ≫ J.map (assemble J X M f)) = _
    rw [← Category.assoc,comparison,biproduct.ι_desc,Category.assoc,← J.map_comp,inclusion_assemble]
    exact hf i

def model : Model J (⨁ X) where
  complex := ⨁ complexes J X M
  bounded := FiniteProjectiveBiproduct.bounded _ (fun i => (M i).bounded)
  projective := FiniteProjectiveBiproduct.projective _ (fun i => (M i).projective)
  comparison := comparison J X M
  universal := universal J X M

#print axioms complexes
#print axioms inclusion
#print axioms comparison
#print axioms inclusion_ext
#print axioms assemble
#print axioms inclusion_assemble
#print axioms universal
#print axioms model
end Verification.FiniteStrictModels
