/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.HomotopyContravariant
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Category.Grp.Abelian

/-!
# Coefficient Hom Single

Applying an arbitrary additive contravariant functor to a contraction
onto degree zero gives an actual concentrated coefficient complex.
-/

noncomputable section
namespace Verification.CoefficientHomSingle

open Classical CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
  Verification.HomotopyContravariant

universe u v u' v'
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
variable (F : Cᵒᵖ ⥤ D) [F.Additive]
variable {ι : Type*} [DecidableEq ι] (c : ComplexShape ι) (j : ι) (B : C)

def singleIso : complex F ((single C c j).obj B) ≅
    (single D c.symm j).obj (F.obj (op B)) :=
  HomologicalComplex.Hom.isoOfComponents (fun i=>by
    by_cases hi : i=j
    · subst i
      exact F.mapIso (singleObjXSelf c j B).op.symm ≪≫ (singleObjXSelf c.symm j _).symm
    · exact (F.map_isZero (isZero_single_obj_X c j B i hi).op).iso
        (isZero_single_obj_X c.symm j _ i hi)) (by
      intro i k _
      change _ ≫ ((single D c.symm j).obj (F.obj (op B))).d i k =
        F.map (((single C c j).obj B).d k i).op ≫ _
      simp only [single_obj_d,op_zero,Functor.map_zero,zero_comp,comp_zero])

variable {c j B}
def equivalence {X : HomologicalComplex C c}
    (e : HomotopyEquiv X ((single C c j).obj B)) :
    HomotopyEquiv (complex F X) ((single D c.symm j).obj (F.obj (op B))) :=
  (HomotopyContravariant.equivalence F e).trans (HomotopyEquiv.ofIso (singleIso F c j B))

variable (M : C)
def homEquivalence {X : HomologicalComplex C c}
    (e : HomotopyEquiv X ((single C c j).obj B)) :
    HomotopyEquiv (homComplex M X) ((single AddCommGrp.{v} c.symm j).obj
      (AddCommGrp.of (B ⟶ M))) := equivalence (preadditiveYoneda.obj M) e

def homologyIso {X : HomologicalComplex C c}
    (e : HomotopyEquiv X ((single C c j).obj B)) :
    (homComplex M X).homology j ≅ AddCommGrp.of (B ⟶ M) :=
  (homEquivalence M e).toHomologyIso j ≪≫ singleObjHomologySelfIso c.symm j _

theorem homology_vanishes {X : HomologicalComplex C c}
    (e : HomotopyEquiv X ((single C c j).obj B)) (i : ι) (hi : i≠j) :
    IsZero ((homComplex M X).homology i) :=
  (isZero_single_obj_homology c.symm j _ i hi).of_iso ((homEquivalence M e).toHomologyIso i)

#print axioms singleIso
#print axioms equivalence
#print axioms homEquivalence
#print axioms homologyIso
#print axioms homology_vanishes

end Verification.CoefficientHomSingle
