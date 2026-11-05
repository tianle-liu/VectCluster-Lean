/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RelativeFlagBoundary
import Verification.RelativeAffineEquivalence
import Verification.AffineRelativeThom

/-!
# Relative Flag Open Boundary

The coefficient quotient in the localized flag is identified with the
literal principal open of the old closed stratum. Thus the flag boundary
is compared with exactly that original principal-open arrow.
-/
noncomputable section
namespace Verification.RelativeFlagOpenBoundary
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex Opposite
open Verification.CoordinateFlag Verification.CoordinatePurityInput
open Verification.RelativeProductNaturality Verification.RelativeProductAffine
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (R A ι : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype ι] [DecidableEq ι]
variable (x : ι → A) (v : ι)
variable (G : Scheme ⥤ CochainComplex C ℤ) (E : OpenConeExcision.StandardExcision G)
variable (P : StandardPurity R G) (N : CoordinatePurityNaturality.Standard R G P)
local notation "Q₀" => ClosedOld A ι x v
local notation "Q₁" => CoordinateLocalizationPair.OpenRing A ι x v ⧸
  ConormalFrame.ideal (CoordinateLocalizationPair.coordinate A ι x v)
local notation "F" => RelativeProductFunctor.thom R (Old ι v) G
variable (FA : Frame R A (Old ι v) (oldCoordinate A ι x v))
variable (localFrame : Frame R (CoordinateLocalizationPair.OpenRing A ι x v) (Old ι v)
  (CoordinateLocalizationPair.coordinate A ι x v))

def openArrow : (F).obj (affineOver R (OpenOld A ι x v)) ⟶ (F).obj (affineOver R Q₀) :=
  (F).map (affineMap R Q₀ (OpenOld A ι x v) (IsScalarTower.toAlgHom R Q₀ (OpenOld A ι x v)))

def coefficientIso : (F).obj (affineOver R (OpenOld A ι x v)) ≅ (F).obj (affineOver R Q₁) :=
  (F).mapIso (RelativeAffineEquivalence.affineIso R Q₁ (OpenOld A ι x v)
    (CoordinateFlagLocalization.closedEquiv R A ι x v))

omit [Fintype ι] [DecidableEq ι] [HasDerivedCategory C] in
theorem open_square : (coefficientIso R A ι x v G).hom ≫ RelativeFlagBoundary.arrow R A ι x v G =
    openArrow R A ι x v G := by
  simp only [coefficientIso,CategoryTheory.Functor.mapIso_hom,RelativeAffineEquivalence.affineIso,
    RelativeFlagBoundary.arrow,openArrow,← CategoryTheory.Functor.map_comp,
    RelativeAffineEquivalence.affineMap_comp]
  apply congrArg (fun f => (F).map (affineMap R Q₀ (OpenOld A ι x v) f))
  exact CoordinateFlagPurity.closedAlgHom_open R A ι x v

def oldIso : oldRelative A ι x v G ≅ DerivedCategory.Q.obj ((F).obj (affineOver R (OpenOld A ι x v))) :=
  RelativeFlagBoundary.oldIso R A ι x v G E P localFrame ≪≫
    (DerivedCategory.Q.mapIso (coefficientIso R A ι x v G)).symm

include N in
theorem ordinary_square : DerivedCategory.Q.map (NestedConeBoundary.supportMap
      (firstArrow A ι x v G) (secondArrow A ι x G)) ≫
      (RelativeFlagBoundary.totalIso R A ι x v G P FA).hom =
    (oldIso R A ι x v G E P localFrame).hom ≫ DerivedCategory.Q.map (openArrow R A ι x v G) := by
  rw [RelativeFlagBoundary.ordinary_square R A ι x v G E P N FA localFrame]
  simp only [oldIso,Iso.trans_hom,Iso.symm_hom]
  rw [← open_square R A ι x v G,CategoryTheory.Functor.map_comp]
  simp only [Category.assoc,CategoryTheory.Functor.mapIso_inv,← CategoryTheory.Functor.map_comp,
    Iso.inv_hom_id_assoc]

def coneIso : fullRelative A ι x G ≅ DerivedCategory.Q.obj (mappingCone (openArrow R A ι x v G)) :=
  NestedPurityBoundary.coordinateIso (openArrow R A ι x v G) A ι x v G
    (oldIso R A ι x v G E P localFrame) (RelativeFlagBoundary.totalIso R A ι x v G P FA)
      (ordinary_square R A ι x v G E P N FA localFrame)

theorem positive_boundary : (coneIso R A ι x v G E P N FA localFrame).hom ≫
    TransverseDerivedBoundary.boundary (openArrow R A ι x v G) =
      CoordinateFlag.boundary A ι x v G ≫
        (DerivedConeArrow.shiftedIso (oldIso R A ι x v G E P localFrame)).hom :=
  NestedPurityBoundary.coordinate_boundary _ _ _ _ _ _ _ _ _

omit [Fintype ι] [DecidableEq ι] [HasDerivedCategory C] in
theorem openArrow_affineTheory : openArrow R A ι x v G =
    (AffineRelativeThom.theory R (Old ι v) G).map
      (IsScalarTower.toAlgHom R Q₀ (OpenOld A ι x v)).toUnder.op := rfl

#print axioms openArrow
#print axioms coefficientIso
#print axioms open_square
#print axioms oldIso
#print axioms ordinary_square
#print axioms coneIso
#print axioms positive_boundary
#print axioms openArrow_affineTheory
end Verification.RelativeFlagOpenBoundary
