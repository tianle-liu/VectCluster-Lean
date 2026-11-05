/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LocalizedCoordinatePurity
import Verification.RelativeFlagOpenBoundary

/-!
# Localized Flag Pairs

The ordinary support square of an ordered coordinate flag after ambient
localization. Purity is used only in D; all other maps come from the actual
quotient/localization squares of rings and their scheme mapping cones.
-/
noncomputable section
namespace Verification.LocalizedFlagPairs
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.CoordinateFlag Verification.CoordinatePurityInput
open Verification.RelativeProductNaturality Verification.RelativeProductAffine
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable {D : Type*} [Category D]
variable (L : DerivedCategory C ⥤ D)
variable (R A ι : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype ι] [DecidableEq ι]
variable (x : ι → A) (v : ι)
variable (G : Scheme ⥤ CochainComplex C ℤ) (E : OpenConeExcision.StandardExcision G)
variable (P : LocalizedCoordinatePurity.Standard L R G)
variable (N : LocalizedCoordinatePurity.Naturality L R G P)
local notation "S" => CoordinateLocalizationPair.OpenRing A ι x v
local notation "y" => CoordinateLocalizationPair.coordinate A ι x v
local notation "Q₀" => ClosedOld A ι x v
local notation "Q₁" => CoordinateLocalizationPair.OpenRing A ι x v ⧸
  ConormalFrame.ideal (CoordinateLocalizationPair.coordinate A ι x v)
variable (oldFrame : Frame R A (Old ι v) (oldCoordinate A ι x v))
variable (localFrame : Frame R (CoordinateLocalizationPair.OpenRing A ι x v) (Old ι v)
  (CoordinateLocalizationPair.coordinate A ι x v))

def oldComparison : L.obj (oldRelative A ι x v G) ≅ L.obj (normalThom S (Old ι v) y G) :=
  (L.mapIso (CoordinateLocalizationPair.oldRelativeIso A ι x v G E)).symm ≪≫
    P.comparison S (Old ι v) y localFrame

def totalComparison : L.obj (DerivedCategory.Q.obj (mappingCone
    (firstArrow A ι x v G ≫ secondArrow A ι x G))) ≅
    L.obj (normalThom A (Old ι v) (oldCoordinate A ι x v) G) :=
  L.mapIso (CoordinateFlagSupport.totalIso A ι x v G) ≪≫
    P.comparison A (Old ι v) (oldCoordinate A ι x v) oldFrame

include N in
theorem ordinary_naturality : L.map (DerivedCategory.Q.map (NestedConeBoundary.supportMap
      (firstArrow A ι x v G) (secondArrow A ι x G))) ≫
      (totalComparison L R A ι x v G P oldFrame).hom =
    (oldComparison L R A ι x v G E P localFrame).hom ≫
      L.map (CoordinatePurityNaturality.normalMap G (oldCoordinate A ι x v) y
        (algebraMap A S) (fun _ => rfl)) := by
  rw [← cancel_epi (L.map (CoordinateLocalizationPair.oldRelativeIso A ι x v G E).hom)]
  simp only [totalComparison, oldComparison, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv,
    ← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [Category.assoc (CoordinateLocalizationPair.oldRelativeIso A ι x v G E).hom,
    CoordinateFlagSupport.ordinary_square]
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (IsScalarTower.toAlgHom R A S).toRingHom)) :=
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A S))))
  simpa only [CategoryTheory.Functor.map_id, Category.id_comp] using N.open_naturality A S (Old ι v) (oldCoordinate A ι x v) y
    (IsScalarTower.toAlgHom R A S) (fun _ => rfl) oldFrame localFrame

def totalIso : L.obj (DerivedCategory.Q.obj (mappingCone
    (firstArrow A ι x v G ≫ secondArrow A ι x G))) ≅
    L.obj (DerivedCategory.Q.obj ((RelativeProductFunctor.thom R (Old ι v) G).obj (affineOver R Q₀))) :=
  totalComparison L R A ι x v G P oldFrame ≪≫
    (L.mapIso (RelativeProductConeNaturality.derivedIso R Q₀ (Old ι v) G)).symm

def oldIso : L.obj (oldRelative A ι x v G) ≅ L.obj (DerivedCategory.Q.obj
    ((RelativeProductFunctor.thom R (Old ι v) G).obj (affineOver R (OpenOld A ι x v)))) :=
  oldComparison L R A ι x v G E P localFrame ≪≫
    (L.mapIso (RelativeProductConeNaturality.derivedIso R Q₁ (Old ι v) G)).symm ≪≫
    (L.mapIso (DerivedCategory.Q.mapIso (RelativeFlagOpenBoundary.coefficientIso R A ι x v G))).symm

include N in
theorem ordinary_square : L.map (DerivedCategory.Q.map (NestedConeBoundary.supportMap
      (firstArrow A ι x v G) (secondArrow A ι x G))) ≫
      (totalIso L R A ι x v G P oldFrame).hom =
    (oldIso L R A ι x v G E P localFrame).hom ≫
      L.map (DerivedCategory.Q.map (RelativeFlagOpenBoundary.openArrow R A ι x v G)) := by
  rw [← cancel_mono (L.map (RelativeProductConeNaturality.derivedIso R Q₀ (Old ι v) G).hom)]
  simp only [totalIso, oldIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv,
    Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id]
  rw [← RelativeFlagOpenBoundary.open_square R A ι x v G, Functor.map_comp]
  simp only [← Category.assoc, Iso.inv_hom_id_assoc]
  have hn := RelativeProductConeNaturality.derived_naturality R Q₀ Q₁ (Old ι v) G
    (CoordinateFlagPurity.closedAlgHom R A ι x v)
  change DerivedCategory.Q.map (RelativeFlagBoundary.arrow R A ι x v G) ≫ _ = _ at hn
  simp only [Iso.inv_hom_id, Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id, hn, Functor.map_comp]
  simp only [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [CategoryTheory.Functor.map_id, Category.comp_id, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  change L.map (DerivedCategory.Q.map (NestedConeBoundary.supportMap
    (firstArrow A ι x v G) (secondArrow A ι x G))) ≫
      (totalComparison L R A ι x v G P oldFrame).hom ≫
        (𝟙 (L.obj (normalThom A (Old ι v) (oldCoordinate A ι x v) G))) = _
  rw [Category.comp_id]
  exact ordinary_naturality L R A ι x v G E P N oldFrame localFrame

#print axioms oldComparison
#print axioms totalComparison
#print axioms ordinary_naturality
#print axioms totalIso
#print axioms oldIso
#print axioms ordinary_square
end Verification.LocalizedFlagPairs
