/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrincipalFlagComparison
import Verification.LocalizedFlagCoherence
import Verification.LocalizedPrincipalPurity

/-!
# Localized Normalized Flag

The standard ordered-flag compatibility is normalized by an independent
principal-purity comparison and the explicit new-first normal-coordinate
map. Its only external equality concerns these uniform Thom comparison
maps, not a cellular boundary, a symbol formula or an exchange matrix.
-/
noncomputable section
namespace Verification.LocalizedNormalizedFlag
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry CochainComplex
open Verification.CoordinateFlag Verification.CoordinatePurityInput
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]
variable (L : DerivedCategory C ⥤ D) [L.Additive] [L.CommShift ℤ]
variable (R : Type) [CommRing R]
variable (G : Scheme ⥤ CochainComplex C ℤ) (E : OpenConeExcision.StandardExcision G)
variable (P : LocalizedCoordinatePurity.Standard L R G)

structure Standard where
  flag : LocalizedFlagCoherence.Standard L R G E P
  principal : ∀ (ι : Type) [Fintype ι] [LinearOrder ι] (v : ι),
    LocalizedPrincipalPurity.Standard L R (AffineRelativeThom.theory R (Old ι v) G)
      (AffineRelativeThom.theory R (FlagNormalCoordinates.Normals ι v) G ⋙ DerivedCategory.Q ⋙ L)
  normalized : ∀ (A ι : Type) [CommRing A] [Algebra R A] [Fintype ι] [LinearOrder ι]
    (x : ι → A) (v : ι) (fullFrame : Frame R A ι x)
    (oldFrame : Frame R A (Old ι v) (oldCoordinate A ι x v))
    (localFrame : Frame R (CoordinateLocalizationPair.OpenRing A ι x v) (Old ι v)
      (CoordinateLocalizationPair.coordinate A ι x v)),
    (flag.comparison A ι x v fullFrame oldFrame localFrame).iteratedThom =
      L.mapIso (FlagNormalCoordinates.thomIso R A ι x v G) ≪≫
        (principal ι v).comparison (ClosedOld A ι x v) (parameter A ι x v) oldFrame.closedSmooth
          (PrincipalFlagComparison.closed_smooth R A ι x v fullFrame)
          (PrincipalFlagComparison.parameter_regular R A ι x v fullFrame)

variable (K : Standard L R G E P)
variable (A ι : Type) [CommRing A] [Algebra R A] [Fintype ι] [LinearOrder ι]
variable (x : ι → A) (v : ι) (fullFrame : Frame R A ι x)
variable (oldFrame : Frame R A (Old ι v) (oldCoordinate A ι x v))
variable (localFrame : Frame R (CoordinateLocalizationPair.OpenRing A ι x v) (Old ι v)
  (CoordinateLocalizationPair.coordinate A ι x v))

theorem positive_boundary : (P.comparison A ι x fullFrame).hom ≫
    L.map (FlagNormalCoordinates.thomIso R A ι x v G).hom ≫
      ((K.principal ι v).comparison (ClosedOld A ι x v) (parameter A ι x v) oldFrame.closedSmooth
        (PrincipalFlagComparison.closed_smooth R A ι x v fullFrame)
        (PrincipalFlagComparison.parameter_regular R A ι x v fullFrame)).hom ≫
      L.map (TransverseDerivedBoundary.boundary (RelativeFlagOpenBoundary.openArrow R A ι x v G)) =
    L.map (CoordinateFlag.boundary A ι x v G) ≫
      (LocalizedFlagCoherence.shiftedIso L (LocalizedFlagPairs.oldIso L R A ι x v G E P localFrame)).hom := by
  have h := LocalizedFlagCoherence.positive_boundary L R G E P A ι x v fullFrame oldFrame localFrame
    (K.flag.comparison A ι x v fullFrame oldFrame localFrame)
  rw [K.normalized] at h
  simpa only [Iso.trans_hom,Functor.mapIso_hom,Category.assoc] using h

#print axioms Standard
#print axioms positive_boundary
end Verification.LocalizedNormalizedFlag
