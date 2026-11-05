/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictCellAttachment
import Verification.ShiftedComparisonCancel

/-!
# Strict Attachment Projection

The quotient of an actual strict cell attachment retains the full
ambient comparison square. Its sign is determined by the genuine cone
triangle, not supplied as a cellular boundary hypothesis.
-/
noncomputable section
namespace Verification.StrictAttachmentProjection
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CochainComplex
open Verification.StrictSingleModel Verification.StrictProjectiveModel Verification.StrictCellAttachment
open Verification.StrictTriangleHom
universe w
variable {A : Type*} [Category A] [Abelian A] [HasBinaryBiproducts A] [HasDerivedCategory.{w} A]
variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
variable [∀ n : ℤ,(CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]
variable (J : DerivedCategory A ⥤ D) [J.Additive] [J.CommShift ℤ] [J.IsTriangulated]
variable {S : Triangle D} (M : Model J S.obj₁) {d : ℤ} (P : Cell J d S.obj₃)
variable (hS : S ∈ distTriang D) (T : Attachment J M P)

def quotient : (model J M P hS T).complex ⟶ single d P.term :=
  (mappingCone.triangle T.attaching).mor₃ ≫ (shiftNegShift (single d P.term) (1 : ℤ)).hom

omit [HasBinaryBiproducts A] [HasZeroObject D]
  [∀ n : ℤ,(CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D] [J.IsTriangulated] [Preadditive D] [J.Additive] in
theorem sourceComparison_eq (PC : CochainComplex A ℤ)
    (φ : S.obj₃ ⟶ J.obj (DerivedCategory.Q.obj PC)) :
    ActualStrictCone.sourceComparison J PC φ = shifted (DerivedCategory.Q ⋙ J) φ (-1) := by
  simp only [ActualStrictCone.sourceComparison,shifted,Functor.commShiftIso_comp_inv_app,
    Functor.comp_obj,Category.assoc]

def triangleMap : S.invRotate ⟶ (DerivedCategory.Q ⋙ J).mapTriangle.obj
    (mappingCone.triangle T.attaching) :=
  Triangle.homMk _ _ T.triangleMap.hom₁ T.triangleMap.hom₂ T.triangleMap.hom₃
    T.triangleMap.comm₁ T.triangleMap.comm₂ (by
      simpa only [Functor.mapTriangle_obj,Triangle.mk_mor₃,Functor.commShiftIso_comp_hom_app,
        Functor.comp_obj,Functor.comp_map,Functor.map_comp,Category.assoc] using T.triangleMap.comm₃)

omit [J.IsTriangulated] in
theorem quotient_square : S.mor₂ ≫ P.comparison =
    (model J M P hS T).comparison ≫ J.map (DerivedCategory.Q.map (quotient J M P hS T)) := by
  have h := positive_square (DerivedCategory.Q ⋙ J) (triangleMap J M P T)
  have hf : (triangleMap J M P T).hom₁ = shifted (DerivedCategory.Q ⋙ J) P.comparison (-1) := by
    dsimp only [triangleMap,Triangle.homMk_hom₁]
    rw [T.first,sourceComparison_eq]
  rw [hf] at h
  have hh := congrArg (fun a => a ≫ (DerivedCategory.Q ⋙ J).map
    (shiftNegShift (single d P.term) (1 : ℤ)).hom) h
  simp only [Triangle.invRotate_mor₃,Category.assoc] at hh
  rw [ShiftedComparisonCancel.cancel] at hh
  simpa only [shiftNegShift,shiftEquiv,shiftEquiv',Iso.app_hom,Iso.inv_hom_id_app_assoc,Functor.map_comp,
    quotient,Functor.comp_obj,Functor.comp_map,StrictCellAttachment.model,triangleMap,Triangle.homMk_hom₃,Category.assoc]
    using hh

omit [J.IsTriangulated] in
theorem quotient_inclusion : mappingCone.inr T.attaching ≫ quotient J M P hS T = 0 := by
  simp only [quotient,← Category.assoc,mappingCone.inr_triangleδ,zero_comp]

variable [M.complex.IsStrictlyGE (d+1)]

omit [J.IsTriangulated] in
theorem quotient_new : (newTermIso J M P hS T).inv ≫ (quotient J M P hS T).f d ≫
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) d P.term).hom = -𝟙 P.term := by
  dsimp only [newTermIso,SingleCellCone.newIso,quotient,HomologicalComplex.comp_f]
  simp only [Category.assoc]
  rw [mappingCone.inl_v_triangle_mor₃_f_assoc]
  simp only [Preadditive.comp_neg,Preadditive.neg_comp]
  congr 1
  simp only [SingleCellCone.headIso,Iso.trans_inv,shiftNegShift,shiftEquiv,shiftEquiv',
    Iso.app_hom,shiftFunctorCompIsoId,Iso.trans_hom,Iso.symm_hom,NatTrans.comp_app,
    HomologicalComplex.comp_f,CochainComplex.shiftFunctorAdd'_inv_app_f',
    CochainComplex.shiftFunctorZero_hom_app_f,shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq,eqToIso.hom,eqToIso.inv,Category.assoc,
    eqToHom_trans,eqToHom_refl,Category.id_comp,Category.comp_id,Iso.inv_hom_id]
  rw [← Category.assoc _ _ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) d P.term).hom,
    eqToHom_trans,eqToHom_refl,Category.id_comp,Iso.inv_hom_id]

#print axioms quotient
#print axioms sourceComparison_eq
#print axioms triangleMap
#print axioms quotient_square
#print axioms quotient_inclusion
#print axioms quotient_new
end Verification.StrictAttachmentProjection
