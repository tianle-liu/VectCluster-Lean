/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FiniteStrictModels
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
# Strict Single Model

A strict cell is an actual projective object in one specified strict
cochain degree. Its universal property compares all strict derived tests
through J; no statement about ambient homology is made.
-/
noncomputable section
namespace Verification.StrictSingleModel
open CategoryTheory CategoryTheory.Limits
open Verification.StrictTriangleHom Verification.StrictProjectiveModel
attribute [local instance] Abelian.hasFiniteBiproducts
universe w
variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w} A]
variable {D : Type*} [Category D] [Preadditive D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]

abbrev single (d : ℤ) (P : A) : CochainComplex A ℤ := (CochainComplex.singleFunctor A d).obj P

structure Cell (d : ℤ) (X : D) where
  term : A
  projective : Projective term
  comparison : X ⟶ J.obj (DerivedCategory.Q.obj (single d term))
  universal : Universal J comparison

variable {J} {d : ℤ} {X Y : D} (M : Cell J d X)

theorem term_projective (i : ℤ) : Projective ((single d M.term).X i) := by
  by_cases hi : i=d
  · exact Projective.of_iso (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) d M.term i hi).symm M.projective
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) d M.term i hi).projective

def model : Model J X where
  complex := single d M.term
  bounded := ⟨d,d,inferInstance,inferInstance⟩
  projective := term_projective M
  comparison := M.comparison
  universal := M.universal

def ofIso (e : Y ≅ X) : Cell J d Y where
  term := M.term
  projective := M.projective
  comparison := e.hom ≫ M.comparison
  universal := (StrictProjectiveModel.ofIso J e (model M)).universal

def redegree {e : ℤ} (h : d=e) : Cell J e X := h ▸ M

/-- This uses only the usual fully faithful embedding A → D(A), never J. -/
def testEquiv (E : A) : (M.term ⟶ E) ≃
    (X ⟶ J.obj (DerivedCategory.Q.obj (single d E))) :=
  (Functor.FullyFaithful.ofFullyFaithful (DerivedCategory.singleFunctor A d)).homEquiv.trans
    (Equiv.ofBijective (comparison J M.comparison (DerivedCategory.Q.obj (single d E)))
      (M.universal _))

variable [HasFiniteBiproducts D] {ι : Type} [Fintype ι] (T : ι → D) (N : ∀ i,Cell J d (T i))

def sum : Cell J d (⨁ T) where
  term := ⨁ fun i => (N i).term
  projective := {
    factors := fun f e _ => ⟨biproduct.desc (fun i =>
      (N i).projective.factors (biproduct.ι (fun j => (N j).term) i ≫ f) e |>.choose), by
      apply biproduct.hom_ext'
      intro i
      rw [biproduct.ι_desc_assoc]
      exact ((N i).projective.factors _ _).choose_spec⟩ }
  comparison := FiniteStrictModels.comparison J T (fun i => model (N i)) ≫
    J.map (DerivedCategory.Q.map ((CochainComplex.singleFunctor A d).mapBiproduct (fun i => (N i).term)).inv)
  universal := ActualStrictCone.universal_postcompose_iso J _
    (DerivedCategory.Q.mapIso ((CochainComplex.singleFunctor A d).mapBiproduct (fun i => (N i).term)).symm)
    (FiniteStrictModels.universal J T (fun i => model (N i)))

#print axioms single
#print axioms Cell
#print axioms term_projective
#print axioms model
#print axioms ofIso
#print axioms redegree
#print axioms testEquiv
#print axioms sum
end Verification.StrictSingleModel
