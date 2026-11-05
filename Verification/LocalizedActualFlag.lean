/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LocalizedNormalizedFlag
import Verification.ActualNormalizedFlag
import Verification.ActualFlagBoundary

/-!
# Localized Actual Flag

The normalized ordered-flag theorem on the actual independent chart.
All geometric hypotheses follow from AS. The full purity comparison is
fixed, while the new-first normal coordinates and principal comparison
are explicitly constructed, rather than chosen by completing a triangle.
-/
noncomputable section
namespace Verification.LocalizedActualFlag
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry CochainComplex
open Verification.IndependentBasicOpen Verification.IndependentChartIndex
open Verification.IndependentOpenCoordinates Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]
variable (L : DerivedCategory C ⥤ D) [L.Additive] [L.CommShift ℤ]
variable (R κ : Type) [CommRing R] [Nontrivial R] [Fintype κ] (n : ℕ)
variable (J : Finset (Fin n)) (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (v : Selected n J)
variable (G : Scheme ⥤ CochainComplex C ℤ) (E : OpenConeExcision.StandardExcision G)
variable (P : LocalizedCoordinatePurity.Standard L R G)
variable (N : LocalizedNormalizedFlag.Standard L R G E P)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hJ : Independent (laterWeights κ n B) J)
variable (hf : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B J))
variable (hs : FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B J)))
local notation "A" => BasicOpen R κ n J B
local notation "Sel" => Selected n J
local notation "x" => selectedCoordinate R κ n J B

def principal : LocalizedPrincipalPurity.Standard L R
    (AffineRelativeThom.theory R (CoordinateFlag.Old Sel v) G)
    (AffineRelativeThom.theory R (FlagNormalCoordinates.Normals Sel v) G ⋙ DerivedCategory.Q ⋙ L) :=
  @N.principal Sel (inferInstance : Fintype Sel) (ActualNormalizedFlag.selectedOrder n J) v

def oldIso := LocalizedFlagPairs.oldIso L R A Sel x v G E P
  (LocalizedOldCoordinateFrame.frame R κ n J B v hpos hneg hsupport hJ hf hs)

def iteratedComparison := L.mapIso (FlagNormalCoordinates.thomIso R A Sel x v G) ≪≫
  (principal L R n J v G E P N).comparison (CoordinateFlag.ClosedOld A Sel x v)
    (CoordinateFlag.parameter A Sel x v)
    (OldCoordinateFrame.frame R κ n J B hpos hneg hsupport hJ hf hs v).closedSmooth
    (PrincipalFlagComparison.closed_smooth R A Sel x v
      (IndependentCoordinatePurity.frame R κ n J B hpos hneg hsupport hJ hf hs))
    (PrincipalFlagComparison.parameter_regular R A Sel x v
      (IndependentCoordinatePurity.frame R κ n J B hpos hneg hsupport hJ hf hs))

theorem positive_boundary :
    (P.comparison A Sel x (IndependentCoordinatePurity.frame R κ n J B hpos hneg hsupport hJ hf hs)).hom ≫
      (iteratedComparison L R κ n J B v G E P N hpos hneg hsupport hJ hf hs).hom ≫
        L.map (TransverseDerivedBoundary.boundary (RelativeFlagOpenBoundary.openArrow R A Sel x v G)) =
    L.map (CoordinateFlag.boundary A Sel x v G) ≫
      (LocalizedFlagCoherence.shiftedIso L (oldIso L R κ n J B v G E P hpos hneg hsupport hJ hf hs)).hom := by
  letI : LinearOrder Sel := ActualNormalizedFlag.selectedOrder n J
  have h := LocalizedNormalizedFlag.positive_boundary L R G E P N A Sel x v
    (IndependentCoordinatePurity.frame R κ n J B hpos hneg hsupport hJ hf hs)
    (OldCoordinateFrame.frame R κ n J B hpos hneg hsupport hJ hf hs v)
    (LocalizedOldCoordinateFrame.frame R κ n J B v hpos hneg hsupport hJ hf hs)
  simpa only [iteratedComparison,Functor.mapIso_hom,Iso.trans_hom,principal,
    oldIso,Category.assoc] using h

#print axioms oldIso
#print axioms principal
#print axioms iteratedComparison
#print axioms positive_boundary
end Verification.LocalizedActualFlag
