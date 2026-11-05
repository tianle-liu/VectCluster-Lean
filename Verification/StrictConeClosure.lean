/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictUniversalShift

/-!
# Strict Cone Closure

A cone acquires its strict universal property from the two given outer
strict resolutions. Its derived arrow is uniquely lifted by representability;
the middle comparison is constructed by the triangle-morphism axiom.
-/
noncomputable section
namespace Verification.StrictConeClosure
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Verification.StrictTriangleHom Verification.StrictUniversalShift
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Preadditive C] [Preadditive D]
variable [HasShift C ℤ] [HasShift D ℤ]
variable [HasZeroObject C] [HasZeroObject D]
variable [∀ (n : ℤ), (shiftFunctor C n).Additive]
variable [∀ (n : ℤ), (shiftFunctor D n).Additive]
variable [Pretriangulated C] [Pretriangulated D]
variable (J : C ⥤ D) [J.Additive] [J.CommShift ℤ]

def rotateMap {T : Triangle C} {S : Triangle D} (φ : S ⟶ J.mapTriangle.obj T) :
    S.rotate ⟶ J.mapTriangle.obj T.rotate :=
  (rotate D).map φ ≫ J.mapTriangleRotateIso.hom.app T

theorem universal_third {T : Triangle C} {S : Triangle D} (φ : S ⟶ J.mapTriangle.obj T)
    (hT : T ∈ distTriang C) (hS : S ∈ distTriang D)
    (h₁ : Universal J φ.hom₁) (h₂ : Universal J φ.hom₂) : Universal J φ.hom₃ := by
  have h := universal_middle J (rotateMap J φ) (rot_of_distTriang T hT) (rot_of_distTriang S hS)
  have hh₁ : (rotateMap J φ).hom₁ = φ.hom₂ := by simp [rotateMap]
  have hh₂ : (rotateMap J φ).hom₂ = φ.hom₃ := by simp [rotateMap]
  have hh₃ : (rotateMap J φ).hom₃ = shifted J φ.hom₁ 1 := by simp [rotateMap, shifted]
  rw [hh₁,hh₂,hh₃] at h
  exact h h₂ (universal_shifted J φ.hom₁ h₁ 1)

variable {S : Triangle D} {PA PC : C}
variable (φA : S.obj₁ ⟶ J.obj PA) (φC : S.obj₃ ⟶ J.obj PC)
variable (hC : Universal J φC)

def connectingArrow : PC⟦(-1 : ℤ)⟧ ⟶ PA :=
  ((universal_shifted J φC hC (-1)) PA).surjective
    (S.invRotate.mor₁ ≫ φA) |>.choose

omit [HasZeroObject C] [HasZeroObject D]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D] in
theorem connecting_square : S.invRotate.mor₁ ≫ φA =
    shifted J φC (-1) ≫ J.map (connectingArrow J φA φC hC) :=
  (((universal_shifted J φC hC (-1)) PA).surjective
    (S.invRotate.mor₁ ≫ φA)).choose_spec.symm

omit [HasZeroObject C] [HasZeroObject D]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D] in
theorem connecting_unique (f : PC⟦(-1 : ℤ)⟧ ⟶ PA)
    (hf : S.invRotate.mor₁ ≫ φA = shifted J φC (-1) ≫ J.map f) :
    f = connectingArrow J φA φC hC := by
  apply ((universal_shifted J φC hC (-1)) PA).injective
  exact hf.symm.trans (connecting_square J φA φC hC)

variable [J.IsTriangulated]

theorem complete_strict_square {T : Triangle C} {U : Triangle D}
    (hT : T ∈ distTriang C) (hU : U ∈ distTriang D)
    (a : U.obj₁ ⟶ J.obj T.obj₁) (b : U.obj₂ ⟶ J.obj T.obj₂)
    (square : U.mor₁ ≫ b = a ≫ J.map T.mor₁)
    (ha : Universal J a) (hb : Universal J b) :
    ∃ c : U.obj₃ ⟶ J.obj T.obj₃, U.mor₂ ≫ c = b ≫ J.map T.mor₂ ∧ Universal J c := by
  obtain ⟨c,hc₁,hc₂⟩ := complete_distinguished_triangle_morphism U (J.mapTriangle.obj T)
    hU (J.map_distinguished T hT) a b square
  let m := Triangle.homMk U (J.mapTriangle.obj T) a b c square hc₁ hc₂
  exact ⟨c,hc₁,universal_third J m hT hU ha hb⟩

/-- Any actual distinguished cone on the lifted arrow has a strict comparison.
The conclusion is the universal Hom property, not an ambient isomorphism. -/
theorem cone_comparison (hS : S ∈ distTriang D) (hA : Universal J φA)
    {PB : C} (g : PA ⟶ PB) (h : PB ⟶ (PC⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (connectingArrow J φA φC hC) g h ∈ distTriang C) :
    ∃ φB : S.obj₂ ⟶ J.obj PB,
      S.mor₁ ≫ φB = φA ≫ J.map g ∧ Universal J φB := by
  let T := Triangle.mk (connectingArrow J φA φC hC) g h
  obtain ⟨φB,hb,hc⟩ := complete_distinguished_triangle_morphism S.invRotate (J.mapTriangle.obj T)
    (inv_rot_of_distTriang S hS) (J.map_distinguished T hT)
    (shifted J φC (-1)) φA (connecting_square J φA φC hC)
  let m : S.invRotate ⟶ J.mapTriangle.obj T :=
    Triangle.homMk _ _ (shifted J φC (-1)) φA φB
      (connecting_square J φA φC hC) hb hc
  exact ⟨φB,hb,universal_third J m hT (inv_rot_of_distTriang S hS)
    (universal_shifted J φC hC (-1)) hA⟩

/-- Existence of a strict middle resolution follows without derived full faithfulness. -/
theorem exists_cone_resolution (hS : S ∈ distTriang D) (hA : Universal J φA) :
    ∃ (PB : C) (g : PA ⟶ PB) (h : PB ⟶ (PC⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧),
      (Triangle.mk (connectingArrow J φA φC hC) g h ∈ distTriang C) ∧
      ∃ φB : S.obj₂ ⟶ J.obj PB, S.mor₁ ≫ φB = φA ≫ J.map g ∧ Universal J φB := by
  obtain ⟨PB,g,h,hT⟩ := distinguished_cocone_triangle (connectingArrow J φA φC hC)
  exact ⟨PB,g,h,hT,cone_comparison J φA φC hC hS hA g h hT⟩

#print axioms rotateMap
#print axioms universal_third
#print axioms connectingArrow
#print axioms connecting_square
#print axioms connecting_unique
#print axioms complete_strict_square
#print axioms cone_comparison
#print axioms exists_cone_resolution
end Verification.StrictConeClosure
