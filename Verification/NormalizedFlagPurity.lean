/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrincipalFlagComparison
import Verification.FlagPurityCoherence

/-!
# Normalized Flag Purity

The standard ordered-flag compatibility is normalized by an independent
principal-purity comparison and the explicit new-first normal-coordinate
map. Its only external equality concerns these uniform Thom comparison
maps, not a cellular boundary, a symbol formula or an exchange matrix.
-/
noncomputable section
namespace Verification.NormalizedFlagPurity
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.CoordinateFlag Verification.CoordinatePurityInput
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (R : Type) [CommRing R]
variable (G : Scheme ⥤ CochainComplex C ℤ) (E : OpenConeExcision.StandardExcision G)
variable (P : StandardPurity R G)

structure Standard where
  flag : FlagPurityCoherence.Standard R G E P
  principal : ∀ (ι : Type) [Fintype ι] [LinearOrder ι] (v : ι),
    PrincipalObjectPurity.Standard R (AffineRelativeThom.theory R (Old ι v) G)
      (AffineRelativeThom.theory R (FlagNormalCoordinates.Normals ι v) G ⋙ DerivedCategory.Q)
  normalized : ∀ (A ι : Type) [CommRing A] [Algebra R A] [Fintype ι] [LinearOrder ι]
    (x : ι → A) (v : ι) (fullFrame : Frame R A ι x)
    (oldFrame : Frame R A (Old ι v) (oldCoordinate A ι x v))
    (localFrame : Frame R (CoordinateLocalizationPair.OpenRing A ι x v) (Old ι v)
      (CoordinateLocalizationPair.coordinate A ι x v)),
    (flag.comparison A ι x v fullFrame oldFrame localFrame).iteratedThom =
      PrincipalFlagComparison.comparison R A ι x v fullFrame G oldFrame (principal ι v)

variable (K : Standard R G E P)
variable (A ι : Type) [CommRing A] [Algebra R A] [Fintype ι] [LinearOrder ι]
variable (x : ι → A) (v : ι) (fullFrame : Frame R A ι x)
variable (oldFrame : Frame R A (Old ι v) (oldCoordinate A ι x v))
variable (localFrame : Frame R (CoordinateLocalizationPair.OpenRing A ι x v) (Old ι v)
  (CoordinateLocalizationPair.coordinate A ι x v))

theorem positive_boundary : (P.comparison A ι x fullFrame).hom ≫
    (FlagNormalCoordinates.thomIso R A ι x v G).hom ≫
      ((K.principal ι v).comparison (ClosedOld A ι x v) (parameter A ι x v) oldFrame.closedSmooth
        (PrincipalFlagComparison.closed_smooth R A ι x v fullFrame)
        (PrincipalFlagComparison.parameter_regular R A ι x v fullFrame)).hom ≫
      TransverseDerivedBoundary.boundary (RelativeFlagOpenBoundary.openArrow R A ι x v G) =
    CoordinateFlag.boundary A ι x v G ≫
      (DerivedConeArrow.shiftedIso (RelativeFlagOpenBoundary.oldIso R A ι x v G E P localFrame)).hom := by
  have h := FlagPurityCoherence.positive_boundary R G E P A ι x v fullFrame oldFrame localFrame
    (K.flag.comparison A ι x v fullFrame oldFrame localFrame)
  rw [K.normalized] at h
  simpa only [PrincipalFlagComparison.comparison,Iso.trans_hom,Category.assoc] using h

#print axioms Standard
#print axioms positive_boundary
end Verification.NormalizedFlagPurity
