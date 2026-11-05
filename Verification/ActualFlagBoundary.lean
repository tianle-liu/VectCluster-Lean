/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RelativeFlagOpenBoundary
import Verification.ActualFlagArrow
import Verification.LocalizedOldCoordinateFrame

/-!
# Actual Flag Boundary

The original independent chart satisfies all geometric conditions of
the flag calculation. The resulting comparison is to the literal
transverse exchange cone with its positive boundary. Coherence with a
single full-coordinate purity choice is a separate standard input.
-/
noncomputable section
namespace Verification.ActualFlagBoundary
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.IndependentBasicOpen Verification.IndependentChartIndex
open Verification.IndependentOpenCoordinates Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (R κ : Type) [CommRing R] [Nontrivial R] [Fintype κ] (n : ℕ)
variable (J : Finset (Fin n)) (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (v : Selected n J)
variable (G : Scheme ⥤ CochainComplex C ℤ) (E : OpenConeExcision.StandardExcision G)
variable (P : CoordinatePurityInput.StandardPurity R G) (N : CoordinatePurityNaturality.Standard R G P)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hJ : Independent (laterWeights κ n B) J)
variable (hf : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B J))
variable (hs : FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B J)))
local notation "A" => BasicOpen R κ n J B
local notation "Sel" => Selected n J
local notation "K" => Other n J ⊕ κ
local notation "Rest" => Other n J
local notation "D" => matrix κ n J B
local notation "x" => selectedCoordinate R κ n J B
local notation "F" => AffineRelativeThom.theory R (CoordinateFlag.Old (Selected n J) v) G

/-- Both old conormal frames are proved from this actual J's AS condition. -/
def oldIso := RelativeFlagOpenBoundary.oldIso R A Sel x v G E P
  (LocalizedOldCoordinateFrame.frame R κ n J B v hpos hneg hsupport hJ hf hs)

def coneIso : CoordinateFlag.fullRelative A Sel x G ≅
    DerivedCategory.Q.obj (mappingCone (ActualTransverseCone.ambientOpen R Sel K Rest Sum.inl D v F)) :=
  RelativeFlagOpenBoundary.coneIso R A Sel x v G E P N
    (OldCoordinateFrame.frame R κ n J B hpos hneg hsupport hJ hf hs v)
    (LocalizedOldCoordinateFrame.frame R κ n J B v hpos hneg hsupport hJ hf hs) ≪≫
      ActualFlagArrow.coneIso R κ n J B v F

theorem positive_boundary : (coneIso R κ n J B v G E P N hpos hneg hsupport hJ hf hs).hom ≫
    TransverseDerivedBoundary.boundary (ActualTransverseCone.ambientOpen R Sel K Rest Sum.inl D v F) =
      CoordinateFlag.boundary A Sel x v G ≫
        (DerivedConeArrow.shiftedIso (oldIso R κ n J B v G E P hpos hneg hsupport hJ hf hs)).hom ≫
          DerivedCategory.Q.map (((F).mapIso (ActualCoordinateFlag.openEquiv R κ n J B v).toUnder.op).inv⟦(1 : ℤ)⟧') := by
  simp only [coneIso,Iso.trans_hom,Category.assoc,ActualFlagArrow.positive_boundary]
  have h := RelativeFlagOpenBoundary.positive_boundary R A Sel x v G E P N
    (OldCoordinateFrame.frame R κ n J B hpos hneg hsupport hJ hf hs v)
    (LocalizedOldCoordinateFrame.frame R κ n J B v hpos hneg hsupport hJ hf hs)
  have hh := congrArg (fun f => f ≫ DerivedCategory.Q.map
    (((F).mapIso (ActualCoordinateFlag.openEquiv R κ n J B v).toUnder.op).inv⟦(1 : ℤ)⟧')) h
  simpa only [oldIso,Category.assoc] using hh

#print axioms oldIso
#print axioms coneIso
#print axioms positive_boundary
end Verification.ActualFlagBoundary
