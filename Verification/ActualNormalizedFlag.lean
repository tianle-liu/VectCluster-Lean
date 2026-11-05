/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.NormalizedFlagPurity
import Verification.ActualFlagBoundary

/-!
# Actual Normalized Flag

The normalized ordered-flag theorem on the actual independent chart.
All geometric hypotheses follow from AS. The full purity comparison is
fixed, while the new-first normal coordinates and principal comparison
are explicitly constructed, rather than chosen by completing a triangle.
-/
noncomputable section
namespace Verification.ActualNormalizedFlag
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.IndependentBasicOpen Verification.IndependentChartIndex
open Verification.IndependentOpenCoordinates Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (R κ : Type) [CommRing R] [Nontrivial R] [Fintype κ] (n : ℕ)
variable (J : Finset (Fin n)) (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (v : Selected n J)
variable (G : Scheme ⥤ CochainComplex C ℤ) (E : OpenConeExcision.StandardExcision G)
variable (P : CoordinatePurityInput.StandardPurity R G)
variable (N : NormalizedFlagPurity.Standard R G E P)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hJ : Independent (laterWeights κ n B) J)
variable (hf : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B J))
variable (hs : FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B J)))
local notation "A" => BasicOpen R κ n J B
local notation "Sel" => Selected n J
local notation "x" => selectedCoordinate R κ n J B

def selectedOrder : LinearOrder (Selected n J) := { (inferInstance : LinearOrder (Selected n J)) with
  toDecidableEq := (inferInstance : DecidableEq (Selected n J))
  compare := fun a b => @compareOfLessAndEq (Selected n J) a b (inferInstance : LT (Selected n J))
    (inferInstance : Decidable (a < b)) (inferInstance : DecidableEq (Selected n J))
  compare_eq_compareOfLessAndEq := fun _ _ => rfl }

def principal : PrincipalObjectPurity.Standard R
    (AffineRelativeThom.theory R (CoordinateFlag.Old Sel v) G)
    (AffineRelativeThom.theory R (FlagNormalCoordinates.Normals Sel v) G ⋙ DerivedCategory.Q) :=
  @N.principal Sel (inferInstance : Fintype Sel) (selectedOrder n J) v

def iteratedComparison := PrincipalFlagComparison.comparison R A Sel x v
  (IndependentCoordinatePurity.frame R κ n J B hpos hneg hsupport hJ hf hs) G
  (OldCoordinateFrame.frame R κ n J B hpos hneg hsupport hJ hf hs v)
  (principal R n J v G E P N)

theorem positive_boundary :
    (P.comparison A Sel x (IndependentCoordinatePurity.frame R κ n J B hpos hneg hsupport hJ hf hs)).hom ≫
      (iteratedComparison R κ n J B v G E P N hpos hneg hsupport hJ hf hs).hom ≫
        TransverseDerivedBoundary.boundary (RelativeFlagOpenBoundary.openArrow R A Sel x v G) =
    CoordinateFlag.boundary A Sel x v G ≫
      (DerivedConeArrow.shiftedIso (ActualFlagBoundary.oldIso R κ n J B v G E P hpos hneg hsupport hJ hf hs)).hom := by
  letI : LinearOrder Sel := selectedOrder n J
  have h := NormalizedFlagPurity.positive_boundary R G E P N A Sel x v
    (IndependentCoordinatePurity.frame R κ n J B hpos hneg hsupport hJ hf hs)
    (OldCoordinateFrame.frame R κ n J B hpos hneg hsupport hJ hf hs v)
    (LocalizedOldCoordinateFrame.frame R κ n J B v hpos hneg hsupport hJ hf hs)
  simpa only [iteratedComparison,PrincipalFlagComparison.comparison,Iso.trans_hom,principal,
    ActualFlagBoundary.oldIso,Category.assoc] using h

#print axioms selectedOrder
#print axioms principal
#print axioms iteratedComparison
#print axioms positive_boundary
end Verification.ActualNormalizedFlag
