/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.CoordinateFlagSupport
import Verification.CoordinatePurityNaturality
import Verification.CoordinateFlagLocalization

/-!
# Coordinate Flag Purity

Purity naturality is applied to the actual localization map of old
coordinate pairs. Both comparisons have their genuine conormal frames;
the ordinary flag support square is proved using excision.
-/
noncomputable section
namespace Verification.CoordinateFlagPurity
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.CoordinateFlag Verification.CoordinatePurityInput
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (R A ι : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype ι] [DecidableEq ι]
variable (x : ι → A) (v : ι)
variable (G : Scheme ⥤ CochainComplex C ℤ) (E : OpenConeExcision.StandardExcision G)
variable (P : StandardPurity R G) (N : CoordinatePurityNaturality.Standard R G P)
local notation "S" => CoordinateLocalizationPair.OpenRing A ι x v
local notation "y" => CoordinateLocalizationPair.coordinate A ι x v
variable (FA : Frame R A (Old ι v) (oldCoordinate A ι x v))
variable (localFrame : Frame R (CoordinateLocalizationPair.OpenRing A ι x v) (Old ι v)
  (CoordinateLocalizationPair.coordinate A ι x v))

def oldComparison : oldRelative A ι x v G ≅ normalThom S (Old ι v) y G :=
  (CoordinateLocalizationPair.oldRelativeIso A ι x v G E).symm ≪≫ P.comparison S (Old ι v) y localFrame


def totalComparison : DerivedCategory.Q.obj (mappingCone (firstArrow A ι x v G ≫ secondArrow A ι x G)) ≅
    normalThom A (Old ι v) (oldCoordinate A ι x v) G :=
  CoordinateFlagSupport.totalIso A ι x v G ≪≫ P.comparison A (Old ι v) (oldCoordinate A ι x v) FA

include N in
theorem ordinary_naturality : DerivedCategory.Q.map (NestedConeBoundary.supportMap
      (firstArrow A ι x v G) (secondArrow A ι x G)) ≫ (totalComparison R A ι x v G P FA).hom =
    (oldComparison R A ι x v G E P localFrame).hom ≫
      CoordinatePurityNaturality.normalMap G (oldCoordinate A ι x v) y (algebraMap A S) (fun _ => rfl) := by
  rw [← cancel_epi (CoordinateLocalizationPair.oldRelativeIso A ι x v G E).hom]
  simp only [totalComparison, oldComparison, Iso.trans_hom, Iso.symm_hom, ← Category.assoc,
    Iso.hom_inv_id, Category.id_comp]
  rw [Category.assoc (CoordinateLocalizationPair.oldRelativeIso A ι x v G E).hom,
    CoordinateFlagSupport.ordinary_square]
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (IsScalarTower.toAlgHom R A S).toRingHom)) :=
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A S))))
  exact N.open_naturality A S (Old ι v) (oldCoordinate A ι x v) y
    (IsScalarTower.toAlgHom R A S) (fun _ => rfl) FA localFrame

def closedAlgHom : ClosedOld A ι x v →ₐ[R] (S ⧸ ConormalFrame.ideal y) where
  __ := CoordinatePairMap.closedMap (oldCoordinate A ι x v) y (algebraMap A S) (fun _ => rfl)
  commutes' r := by
    change Ideal.Quotient.mk _ (algebraMap A S (algebraMap R A r)) =
      algebraMap R (S ⧸ ConormalFrame.ideal y) r
    rw [← IsScalarTower.algebraMap_apply]
    rfl

omit [Fintype ι] [DecidableEq ι] in
theorem closedAlgHom_open : (CoordinateFlagLocalization.closedEquiv R A ι x v).toAlgHom.comp
    (closedAlgHom R A ι x v) = IsScalarTower.toAlgHom R (ClosedOld A ι x v) (OpenOld A ι x v) := by
  apply AlgHom.ext
  intro a
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective a
  exact CoordinateFlagLocalization.closedEquiv_generator R A ι x v a

#print axioms oldComparison
#print axioms totalComparison
#print axioms ordinary_naturality
#print axioms closedAlgHom
#print axioms closedAlgHom_open
end Verification.CoordinateFlagPurity
