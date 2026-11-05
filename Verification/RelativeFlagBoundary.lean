/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.CoordinateFlagPurity
import Verification.RelativeProductConeNaturality
import Verification.NestedPurityBoundary

/-!
# Relative Flag Boundary

The actual adjacent coordinate boundary is the boundary of the
relative normal-product functor applied to the old closed stratum's
localization. The comparison follows from ordinary purity naturality,
with no assumed equality of connecting maps.
-/
noncomputable section
namespace Verification.RelativeFlagBoundary
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.CoordinateFlag Verification.CoordinatePurityInput
open Verification.RelativeProductNaturality Verification.RelativeProductAffine
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (R A ι : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype ι] [DecidableEq ι]
variable (x : ι → A) (v : ι)
variable (G : Scheme ⥤ CochainComplex C ℤ) (E : OpenConeExcision.StandardExcision G)
variable (P : StandardPurity R G) (N : CoordinatePurityNaturality.Standard R G P)
local notation "S" => CoordinateLocalizationPair.OpenRing A ι x v
local notation "y" => CoordinateLocalizationPair.coordinate A ι x v
local notation "Q₀" => ClosedOld A ι x v
local notation "Q₁" => CoordinateLocalizationPair.OpenRing A ι x v ⧸
  ConormalFrame.ideal (CoordinateLocalizationPair.coordinate A ι x v)
variable (FA : Frame R A (Old ι v) (oldCoordinate A ι x v))
variable (localFrame : Frame R (CoordinateLocalizationPair.OpenRing A ι x v) (Old ι v)
  (CoordinateLocalizationPair.coordinate A ι x v))

def arrow : (RelativeProductFunctor.thom R (Old ι v) G).obj (affineOver R Q₁) ⟶
    (RelativeProductFunctor.thom R (Old ι v) G).obj (affineOver R Q₀) :=
  (RelativeProductFunctor.thom R (Old ι v) G).map
    (affineMap R Q₀ Q₁ (CoordinateFlagPurity.closedAlgHom R A ι x v))

def oldIso : oldRelative A ι x v G ≅
    DerivedCategory.Q.obj ((RelativeProductFunctor.thom R (Old ι v) G).obj (affineOver R Q₁)) :=
  CoordinateFlagPurity.oldComparison R A ι x v G E P localFrame ≪≫
    (RelativeProductConeNaturality.derivedIso R Q₁ (Old ι v) G).symm

def totalIso : DerivedCategory.Q.obj (mappingCone (firstArrow A ι x v G ≫ secondArrow A ι x G)) ≅
    DerivedCategory.Q.obj ((RelativeProductFunctor.thom R (Old ι v) G).obj (affineOver R Q₀)) :=
  CoordinateFlagPurity.totalComparison R A ι x v G P FA ≪≫
    (RelativeProductConeNaturality.derivedIso R Q₀ (Old ι v) G).symm

include N in
theorem ordinary_square : DerivedCategory.Q.map (NestedConeBoundary.supportMap
      (firstArrow A ι x v G) (secondArrow A ι x G)) ≫ (totalIso R A ι x v G P FA).hom =
    (oldIso R A ι x v G E P localFrame).hom ≫ DerivedCategory.Q.map (arrow R A ι x v G) := by
  rw [← cancel_mono (RelativeProductConeNaturality.derivedIso R Q₀ (Old ι v) G).hom]
  simp only [oldIso,totalIso,Iso.trans_hom,Iso.symm_hom,Category.assoc,Iso.inv_hom_id,Category.comp_id]
  rw [show DerivedCategory.Q.map (arrow R A ι x v G) ≫
      (RelativeProductConeNaturality.derivedIso R Q₀ (Old ι v) G).hom =
        (RelativeProductConeNaturality.derivedIso R Q₁ (Old ι v) G).hom ≫
          CoordinatePurityNaturality.normalMap G (oldCoordinate A ι x v) y (algebraMap A S)
            (fun _ => rfl) from
    RelativeProductConeNaturality.derived_naturality R Q₀ Q₁ (Old ι v) G
      (CoordinateFlagPurity.closedAlgHom R A ι x v)]
  simp only [← Category.assoc,Iso.inv_hom_id,Category.id_comp]
  exact CoordinateFlagPurity.ordinary_naturality R A ι x v G E P N FA localFrame

def coneIso : fullRelative A ι x G ≅ DerivedCategory.Q.obj (mappingCone (arrow R A ι x v G)) :=
  NestedPurityBoundary.coordinateIso (arrow R A ι x v G) A ι x v G
    (oldIso R A ι x v G E P localFrame) (totalIso R A ι x v G P FA)
      (ordinary_square R A ι x v G E P N FA localFrame)

theorem positive_boundary : (coneIso R A ι x v G E P N FA localFrame).hom ≫
    TransverseDerivedBoundary.boundary (arrow R A ι x v G) =
      CoordinateFlag.boundary A ι x v G ≫
        (DerivedConeArrow.shiftedIso (oldIso R A ι x v G E P localFrame)).hom :=
  NestedPurityBoundary.coordinate_boundary _ _ _ _ _ _ _ _ _

#print axioms arrow
#print axioms oldIso
#print axioms totalIso
#print axioms ordinary_square
#print axioms coneIso
#print axioms positive_boundary
end Verification.RelativeFlagBoundary
