/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictConeClosure
import Verification.ProjectiveConeTerms
import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Actual Strict Cone

The strict cone comparison on mathlib's actual derived mapping cone.
The only chain-level realization input is surjectivity of Q.map for the
specified projective source/target pair. It says nothing about realization
J being fully faithful, and no middle universal property is supplied.
-/
noncomputable section
namespace Verification.ActualStrictCone
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CochainComplex
open Verification.StrictTriangleHom Verification.StrictUniversalShift Verification.StrictConeClosure
universe v₁ v₂ u₁ u₂ w

section Iso
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Preadditive C] [Preadditive D]
variable (J : C ⥤ D) [J.Additive]

theorem universal_postcompose_iso {P Q : C} {X : D} (φ : X ⟶ J.obj P)
    (e : P ≅ Q) (h : Universal J φ) : Universal J (φ ≫ J.map e.hom) := by
  intro E
  constructor
  · intro f g hfg
    apply (cancel_epi e.hom).mp
    apply (h E).1
    simpa only [comparison, AddMonoidHom.coe_mk, ZeroHom.coe_mk, J.map_comp,
      Category.assoc] using hfg
  · intro u
    obtain ⟨f,hf⟩ := (h E).2 u
    refine ⟨e.inv ≫ f, ?_⟩
    change (φ ≫ J.map e.hom) ≫ J.map (e.inv ≫ f) = u
    rw [Category.assoc, ← J.map_comp, e.hom_inv_id_assoc]
    exact hf
end Iso

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasBinaryBiproducts A]
variable [HasDerivedCategory.{w} A]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
variable [∀ (n : ℤ), (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]
variable (J : DerivedCategory A ⥤ D) [J.Additive] [J.CommShift ℤ] [J.IsTriangulated]
variable {S : Triangle D} (hS : S ∈ distTriang D)
variable (PA PC : CochainComplex A ℤ)
variable (φA : S.obj₁ ⟶ J.obj (DerivedCategory.Q.obj PA))
variable (φC : S.obj₃ ⟶ J.obj (DerivedCategory.Q.obj PC))
variable (hA : Universal J φA) (hC : Universal J φC)

def sourceComparison : S.obj₃⟦(-1 : ℤ)⟧ ⟶ J.obj (DerivedCategory.Q.obj (PC⟦(-1 : ℤ)⟧)) :=
  shifted J φC (-1) ≫ J.map ((DerivedCategory.Q.commShiftIso (-1 : ℤ)).inv.app PC)

omit [HasBinaryBiproducts A] [HasZeroObject D]
  [∀ (n : ℤ), (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]
  [J.IsTriangulated] in
include hC in
theorem source_universal : Universal J (sourceComparison J PC φC) :=
  universal_postcompose_iso J (shifted J φC (-1))
    ((DerivedCategory.Q.commShiftIso (-1 : ℤ)).symm.app PC) (universal_shifted J φC hC (-1))

variable (u : PC⟦(-1 : ℤ)⟧ ⟶ PA)
variable (hu : DerivedCategory.Q.map u = (DerivedCategory.Q.commShiftIso (-1 : ℤ)).hom.app PC ≫
  connectingArrow J φA φC hC)

omit [HasBinaryBiproducts A] [HasZeroObject D]
  [∀ (n : ℤ), (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]
  [J.IsTriangulated] in
include hu in
theorem source_square : S.invRotate.mor₁ ≫ φA =
    sourceComparison J PC φC ≫ J.map (DerivedCategory.Q.map u) := by
  rw [sourceComparison, Category.assoc, ← J.map_comp, hu, Iso.inv_hom_id_app_assoc]
  exact connecting_square J φA φC hC

include hS hA hu in
/-- The actual mapping cone has the required strict universal property. -/
theorem cone_universal :
    ∃ φB : S.obj₂ ⟶ J.obj (DerivedCategory.Q.obj (mappingCone u)),
      S.mor₁ ≫ φB = φA ≫ J.map (DerivedCategory.Q.map (mappingCone.inr u)) ∧ Universal J φB := by
  let T := DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle u)
  have hT : T ∈ distTriang (DerivedCategory A) :=
    (DerivedCategory.mem_distTriang_iff T).mpr ⟨_,_,u,⟨Iso.refl _⟩⟩
  exact complete_strict_square J hT (inv_rot_of_distTriang S hS)
    (sourceComparison J PC φC) φA (source_square J PA PC φA φC hC u hu)
    (source_universal J PC φC hC) hA

include hS hA in
/-- Chain-map representability is the standard input; all middle properties
and all cone-term finiteness/projectivity statements are conclusions. -/
theorem bounded_projective_cone
    (represent : Function.Surjective (DerivedCategory.Q.map :
      (PC⟦(-1 : ℤ)⟧ ⟶ PA) → (DerivedCategory.Q.obj (PC⟦(-1 : ℤ)⟧) ⟶ DerivedCategory.Q.obj PA)))
    (bPA : ProjectiveConeTerms.Bounded PA) (bPC : ProjectiveConeTerms.Bounded PC)
    (pPA : ∀ i, Projective (PA.X i)) (pPC : ∀ i, Projective (PC.X i)) :
    ∃ u : PC⟦(-1 : ℤ)⟧ ⟶ PA,
      DerivedCategory.Q.map u = (DerivedCategory.Q.commShiftIso (-1 : ℤ)).hom.app PC ≫
        connectingArrow J φA φC hC ∧
      ProjectiveConeTerms.Bounded (mappingCone u) ∧
      (∀ i, Projective ((mappingCone u).X i)) ∧
      ∃ φB : S.obj₂ ⟶ J.obj (DerivedCategory.Q.obj (mappingCone u)),
        S.mor₁ ≫ φB = φA ≫ J.map (DerivedCategory.Q.map (mappingCone.inr u)) ∧ Universal J φB := by
  obtain ⟨u,hu⟩ := represent ((DerivedCategory.Q.commShiftIso (-1 : ℤ)).hom.app PC ≫
    connectingArrow J φA φC hC)
  exact ⟨u,hu,ProjectiveConeTerms.bounded u (ProjectiveConeTerms.bounded_shift PC bPC (-1)) bPA,
    ProjectiveConeTerms.term_projective u (ProjectiveConeTerms.shift_projective PC pPC (-1)) pPA,
    cone_universal J hS PA PC φA φC hA hC u hu⟩

#print axioms universal_postcompose_iso
#print axioms sourceComparison
#print axioms source_universal
#print axioms source_square
#print axioms cone_universal
#print axioms bounded_projective_cone
end Verification.ActualStrictCone
