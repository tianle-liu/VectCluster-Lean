/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SingleCellCone

/-!
# Strict Cell Attachment

A strict cellular attachment retains its actual attaching chain map
and the full comparison of distinguished triangles. The comparison's
universal property and the literal cone terms/differential are conclusions.
-/
noncomputable section
namespace Verification.StrictCellAttachment
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CochainComplex
open Verification.StrictSingleModel Verification.StrictProjectiveModel
open Verification.StrictTriangleHom Verification.StrictConeClosure
universe w
variable {A : Type*} [Category A] [Abelian A] [HasBinaryBiproducts A] [HasDerivedCategory.{w} A]
variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
variable [∀ n : ℤ,(CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]
variable (J : DerivedCategory A ⥤ D) [J.Additive] [J.CommShift ℤ] [J.IsTriangulated]
variable {S : Triangle D} (M : Model J S.obj₁) {d : ℤ} (P : Cell J d S.obj₃)

set_option maxHeartbeats 800000 in
structure Attachment where
  attaching : (single d P.term)⟦(-1 : ℤ)⟧ ⟶ M.complex
  represents : DerivedCategory.Q.map attaching =
    (DerivedCategory.Q.commShiftIso (-1 : ℤ)).hom.app (single d P.term) ≫
      connectingArrow J M.comparison P.comparison P.universal
  triangleMap : S.invRotate ⟶ J.mapTriangle.obj
    (DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle attaching))
  first : triangleMap.hom₁ = ActualStrictCone.sourceComparison J (single d P.term) P.comparison
  second : triangleMap.hom₂ = M.comparison

variable (hS : S ∈ distTriang D) (H : ChainRepresentability (A := A))

include hS H in
theorem exists_attachment : Nonempty (Attachment J M P) := by
  obtain ⟨u,hu⟩ := H ((single d P.term)⟦(-1 : ℤ)⟧) M.complex
    (ProjectiveConeTerms.bounded_shift _ (model P).bounded (-1)) M.bounded
    (ProjectiveConeTerms.shift_projective _ (term_projective P) (-1)) M.projective
    ((DerivedCategory.Q.commShiftIso (-1 : ℤ)).hom.app (single d P.term) ≫
      connectingArrow J M.comparison P.comparison P.universal)
  have hsquare := ActualStrictCone.source_square J M.complex (single d P.term)
    M.comparison P.comparison P.universal u hu
  have hT : DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle u) ∈ distTriang (DerivedCategory A) :=
    (DerivedCategory.mem_distTriang_iff _).mpr ⟨_,_,u,⟨Iso.refl _⟩⟩
  obtain ⟨c,hc₁,hc₂⟩ := complete_distinguished_triangle_morphism S.invRotate
    (J.mapTriangle.obj (DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle u)))
    (inv_rot_of_distTriang S hS) (J.map_distinguished _ hT)
    (ActualStrictCone.sourceComparison J (single d P.term) P.comparison) M.comparison hsquare
  exact ⟨⟨u,hu,Triangle.homMk _ _ _ _ c hsquare hc₁ hc₂,rfl,rfl⟩⟩

def attach : Attachment J M P := (exists_attachment J M P hS H).some

variable (T : Attachment J M P)

omit [J.IsTriangulated] in
include hS in
theorem universal : Universal J T.triangleMap.hom₃ := by
  apply universal_third J T.triangleMap
    ((DerivedCategory.mem_distTriang_iff _).mpr ⟨_,_,T.attaching,⟨Iso.refl _⟩⟩)
    (inv_rot_of_distTriang S hS)
  · rw [T.first]
    exact ActualStrictCone.source_universal J _ P.comparison P.universal
  · rw [T.second]
    exact M.universal

def model : Model J S.obj₂ where
  complex := mappingCone T.attaching
  bounded := ProjectiveConeTerms.bounded T.attaching
    (ProjectiveConeTerms.bounded_shift _ (StrictSingleModel.model P).bounded (-1)) M.bounded
  projective := ProjectiveConeTerms.term_projective T.attaching
    (ProjectiveConeTerms.shift_projective _ (term_projective P) (-1)) M.projective
  comparison := T.triangleMap.hom₃
  universal := universal J M P hS T

omit [J.IsTriangulated] in
theorem inclusion_square : S.mor₁ ≫ (model J M P hS T).comparison =
    M.comparison ≫ J.map (DerivedCategory.Q.map (mappingCone.inr T.attaching)) := by
  have h := T.triangleMap.comm₂
  rw [T.second] at h
  exact h

variable [M.complex.IsStrictlyGE (d+1)]

omit [J.IsTriangulated] in
theorem support_lower : (model J M P hS T).complex.IsStrictlyGE d :=
  SingleCellCone.support_lower P.term d M.complex T.attaching

def newTermIso : ((model J M P hS T).complex).X d ≅ P.term :=
  SingleCellCone.newIso P.term d M.complex T.attaching

omit [M.complex.IsStrictlyGE (d+1)] in
def oldTermIso (i : ℤ) (hi : i ≠ d) : ((model J M P hS T).complex).X i ≅ M.complex.X i :=
  SingleCellCone.oldIso P.term d M.complex T.attaching i hi

omit [J.IsTriangulated] in
theorem new_differential :
    (newTermIso J M P hS T).inv ≫ (model J M P hS T).complex.d d (d+1) ≫
      (oldTermIso J M P hS T (d+1) (by omega)).hom =
        (SingleCellCone.headIso P.term d).inv ≫ T.attaching.f (d+1) :=
  SingleCellCone.new_differential P.term d M.complex T.attaching

omit [M.complex.IsStrictlyGE (d+1)] [J.IsTriangulated] in
theorem old_differential (i j : ℤ) (hi : i ≠ d) (hj : j ≠ d) :
    (oldTermIso J M P hS T i hi).inv ≫ (model J M P hS T).complex.d i j ≫
      (oldTermIso J M P hS T j hj).hom = M.complex.d i j :=
  SingleCellCone.old_differential P.term d M.complex T.attaching i j hi hj

variable [M.complex.IsStrictlyLE 0]
omit [M.complex.IsStrictlyGE (d+1)] [J.IsTriangulated] in
theorem support_upper (hd : d ≤ 0) : (model J M P hS T).complex.IsStrictlyLE 0 :=
  SingleCellCone.support_upper P.term d M.complex T.attaching hd

#print axioms Attachment
#print axioms exists_attachment
#print axioms attach
#print axioms universal
#print axioms model
#print axioms inclusion_square
#print axioms support_lower
#print axioms newTermIso
#print axioms oldTermIso
#print axioms new_differential
#print axioms old_differential
#print axioms support_upper
end Verification.StrictCellAttachment
