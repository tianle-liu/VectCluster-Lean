/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Strict Triangle Hom

The Hom five-lemma across two different triangulated categories.
The comparison is f ↦ φ ≫ J.map f. No fullness, faithfulness, or ambient
quasi-isomorphism of the realization functor J is assumed. Exactness comes
from the actual distinguished triangles and their rotations.
-/
noncomputable section
namespace Verification.StrictTriangleHom
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Preadditive C] [Preadditive D]
variable (J : C ⥤ D) [J.Additive]

def comparison {P : C} {X : D} (φ : X ⟶ J.obj P) (E : C) :
    (P ⟶ E) →+ (X ⟶ J.obj E) where
  toFun f := φ ≫ J.map f
  map_zero' := by rw [J.map_zero, comp_zero]
  map_add' f g := by rw [J.map_add, Preadditive.comp_add]

def Universal {P : C} {X : D} (φ : X ⟶ J.obj P) : Prop :=
  ∀ E : C, Function.Bijective (comparison J φ E)

theorem comparison_natural {P Q E : C} {X Y : D}
    (φ : X ⟶ J.obj P) (ψ : Y ⟶ J.obj Q) (a : P ⟶ Q) (b : X ⟶ Y)
    (h : b ≫ ψ = φ ≫ J.map a) (g : Q ⟶ E) :
    comparison J φ E (a ≫ g) = b ≫ comparison J ψ E g := by
  change φ ≫ J.map (a ≫ g) = b ≫ (ψ ≫ J.map g)
  rw [J.map_comp, ← Category.assoc, ← h, Category.assoc]

variable [HasShift C ℤ] [HasShift D ℤ] [J.CommShift ℤ]

def shifted {P : C} {X : D} (φ : X ⟶ J.obj P) (n : ℤ) :
    X⟦n⟧ ⟶ J.obj (P⟦n⟧) :=
  φ⟦n⟧' ≫ (J.commShiftIso n).inv.app P

variable {T : Triangle C} {S : Triangle D} (φ : S ⟶ J.mapTriangle.obj T)

def inverseMap : S.invRotate ⟶ J.mapTriangle.obj T.invRotate :=
  (invRotate D).map φ ≫ (J.mapTriangleInvRotateIso.hom.app T)

omit [J.Additive] [Preadditive C] [Preadditive D] in
theorem positive_square : S.mor₃ ≫ shifted J φ.hom₁ 1 = φ.hom₃ ≫ J.map T.mor₃ := by
  dsimp only [shifted]
  rw [← Category.assoc, φ.comm₃]
  change (φ.hom₃ ≫ (J.map T.mor₃ ≫ (J.commShiftIso (1 : ℤ)).hom.app T.obj₁)) ≫ _ = _
  simp

theorem negative_square : S.invRotate.mor₁ ≫ φ.hom₁ =
    shifted J φ.hom₃ (-1) ≫ J.map T.invRotate.mor₁ := by
  simpa [inverseMap, shifted] using (inverseMap J φ).comm₁


variable [HasZeroObject C] [HasZeroObject D]
variable [∀ (n : ℤ), (shiftFunctor C n).Additive]
variable [∀ (n : ℤ), (shiftFunctor D n).Additive]
variable [Pretriangulated C] [Pretriangulated D]
variable (hT : T ∈ distTriang C) (hS : S ∈ distTriang D) (E : C)

include hT hS in
theorem middle_injective
    (hA : Function.Injective (comparison J φ.hom₁ E))
    (hC : Function.Injective (comparison J φ.hom₃ E))
    (hA1 : Function.Surjective (comparison J (shifted J φ.hom₁ 1) E)) :
    Function.Injective (comparison J φ.hom₂ E) := by
  have hz : ∀ f : T.obj₂ ⟶ E, comparison J φ.hom₂ E f = 0 → f = 0 := by
    intro f hf
    have ha : T.mor₁ ≫ f = 0 := by
      apply hA
      rw [comparison_natural J φ.hom₁ φ.hom₂ T.mor₁ S.mor₁ φ.comm₁ f, hf,
        comp_zero, map_zero]
    obtain ⟨g,hg⟩ := T.yoneda_exact₂ hT f ha
    have hc : S.mor₂ ≫ comparison J φ.hom₃ E g = 0 := by
      rw [← comparison_natural J φ.hom₂ φ.hom₃ T.mor₂ S.mor₂ φ.comm₂ g, ← hg, hf]
    obtain ⟨u,hu⟩ := S.yoneda_exact₃ hS (comparison J φ.hom₃ E g) hc
    obtain ⟨k,hk⟩ := hA1 u
    rw [← hk] at hu
    have hh : g = T.mor₃ ≫ k := by
      apply hC
      change φ.hom₃ ≫ J.map g = φ.hom₃ ≫ J.map (T.mor₃ ≫ k)
      rw [J.map_comp, ← Category.assoc]
      rw [← positive_square J φ, Category.assoc]
      exact hu
    rw [hg, hh, ← Category.assoc, comp_distTriang_mor_zero₂₃ T hT, zero_comp]
  intro f g h
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub, h, sub_self]

include hT hS in
theorem middle_surjective
    (hA : Function.Surjective (comparison J φ.hom₁ E))
    (hC : Function.Surjective (comparison J φ.hom₃ E))
    (hCneg : Function.Injective (comparison J (shifted J φ.hom₃ (-1)) E)) :
    Function.Surjective (comparison J φ.hom₂ E) := by
  intro u
  obtain ⟨f,hf⟩ := hA (S.mor₁ ≫ u)
  have hd : T.invRotate.mor₁ ≫ f = 0 := by
    apply hCneg
    change shifted J φ.hom₃ (-1) ≫ J.map (T.invRotate.mor₁ ≫ f) =
      shifted J φ.hom₃ (-1) ≫ J.map 0
    rw [J.map_comp, J.map_zero, comp_zero, ← Category.assoc, ← negative_square J φ,
      Category.assoc]
    change S.invRotate.mor₁ ≫ comparison J φ.hom₁ E f = 0
    rw [hf, ← Category.assoc]
    change (S.invRotate.mor₁ ≫ S.invRotate.mor₂) ≫ u = 0
    rw [comp_distTriang_mor_zero₁₂ S.invRotate (inv_rot_of_distTriang S hS), zero_comp]
  obtain ⟨v,hv⟩ := T.invRotate.yoneda_exact₂ (inv_rot_of_distTriang T hT) f hd
  change T.obj₂ ⟶ E at v
  change f = T.mor₁ ≫ v at hv
  have hu : S.mor₁ ≫ (u - comparison J φ.hom₂ E v) = 0 := by
    rw [Preadditive.comp_sub,
      ← comparison_natural J φ.hom₁ φ.hom₂ T.mor₁ S.mor₁ φ.comm₁ v, ← hv, hf, sub_self]
  obtain ⟨w,hw⟩ := S.yoneda_exact₂ hS (u - comparison J φ.hom₂ E v) hu
  obtain ⟨g,hg⟩ := hC w
  refine ⟨v + T.mor₂ ≫ g, ?_⟩
  rw [map_add, comparison_natural J φ.hom₂ φ.hom₃ T.mor₂ S.mor₂ φ.comm₂ g, hg, ← hw]
  exact add_sub_cancel _ _

include hT hS in
theorem middle_bijective
    (hA : Function.Bijective (comparison J φ.hom₁ E))
    (hC : Function.Bijective (comparison J φ.hom₃ E))
    (hA1 : Function.Surjective (comparison J (shifted J φ.hom₁ 1) E))
    (hCneg : Function.Injective (comparison J (shifted J φ.hom₃ (-1)) E)) :
    Function.Bijective (comparison J φ.hom₂ E) :=
  ⟨middle_injective J φ hT hS E hA.1 hC.1 hA1,
    middle_surjective J φ hT hS E hA.2 hC.2 hCneg⟩

#print axioms comparison
#print axioms Universal
#print axioms comparison_natural
#print axioms shifted
#print axioms inverseMap
#print axioms positive_square
#print axioms negative_square
#print axioms middle_injective
#print axioms middle_surjective
#print axioms middle_bijective
end Verification.StrictTriangleHom
