/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LocalizedActualFlag
import Verification.LocalizedActualPrincipal

/-!
# Localized Actual Transverse

The fixed full-coordinate purity comparison on the original chart is
now connected to the original transverse principal boundary. Every ring,
open map, closed map and new-first normal-coordinate map is the actual
constructed one; the only coherence inputs are the uniform standard
purity statements, not a paper-specific differential equation.
-/
noncomputable section
namespace Verification.LocalizedActualTransverse
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex Opposite
open Verification.IndependentBasicOpen Verification.IndependentChartIndex
open Verification.IndependentOpenCoordinates Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable {Z : Type*} [Category Z] [Preadditive Z] [HasShift Z ℤ]
variable (L : DerivedCategory C ⥤ Z) [L.Additive] [L.CommShift ℤ]
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
local notation "K" => Other n J ⊕ κ
local notation "Rest" => Other n J
local notation "D" => matrix κ n J B
local notation "x" => selectedCoordinate R κ n J B
local notation "F" => AffineRelativeThom.theory R (CoordinateFlag.Old (Selected n J) v) G
local notation "T" => AffineRelativeThom.theory R (FlagNormalCoordinates.Normals (Selected n J) v) G ⋙ DerivedCategory.Q ⋙ L
local notation "Q" => LocalizedActualFlag.principal L R n J v G E P N
local notation "hD" => matrix_zero_block κ n J B hpos hneg hsupport hJ

def normalIso : L.obj (CoordinatePurityInput.normalThom A Sel x G) ≅
    (T).obj (op (CommRingCat.mkUnder (CommRingCat.of R)
      (ActualTransverseLocalization.ClosedSource R Sel K Rest Sum.inl D v))) :=
  L.mapIso (FlagNormalCoordinates.thomIso R A Sel x v G) ≪≫
    ((T).mapIso (ActualCoordinateFlag.closedEquiv R κ n J B v).toUnder.op).symm

def adjacentBoundary :=
  (LocalizedActualPrincipal.ambientIso R κ n J B v hD hf hs L F T Q).hom ≫
    L.map (TransverseDerivedBoundary.boundary (ActualTransverseCone.ambientOpen R Sel K Rest Sum.inl D v F))

theorem positive_boundary :
    (P.comparison A Sel x (IndependentCoordinatePurity.frame R κ n J B hpos hneg hsupport hJ hf hs)).hom ≫
      (normalIso L R κ n J B v G).hom ≫ (adjacentBoundary L R κ n J B v G E P N hpos hneg hsupport hJ hf hs) =
    L.map (CoordinateFlag.boundary A Sel x v G) ≫
      (LocalizedFlagCoherence.shiftedIso L (LocalizedActualFlag.oldIso L R κ n J B v G E P hpos hneg hsupport hJ hf hs)).hom ≫
        L.map (DerivedCategory.Q.map (((F).mapIso (ActualCoordinateFlag.openEquiv R κ n J B v).toUnder.op).inv⟦(1 : ℤ)⟧')) := by
  simp only [normalIso,Iso.trans_hom,Iso.symm_hom,adjacentBoundary,Functor.mapIso_hom,Category.assoc]
  rw [← Category.assoc ((T).mapIso (ActualCoordinateFlag.closedEquiv R κ n J B v).toUnder.op).inv,
    ← LocalizedActualPrincipal.comparison_transport R κ n J B v hD hf hs L F T Q]
  have hb := ActualFlagArrow.positive_boundary R κ n J B v F
  have hl := congrArg (fun f => L.map f) hb
  simp only [Functor.map_comp] at hl
  simp only [Category.assoc, hl]
  have h := LocalizedActualFlag.positive_boundary L R κ n J B v G E P N hpos hneg hsupport hJ hf hs
  have hh := congrArg (fun f => f ≫ L.map (DerivedCategory.Q.map
    (((F).mapIso (ActualCoordinateFlag.openEquiv R κ n J B v).toUnder.op).inv⟦(1 : ℤ)⟧'))) h
  simpa only [LocalizedActualFlag.iteratedComparison,
    LocalizedActualPrincipal.flagIso,Iso.trans_hom,Functor.mapIso_hom,Category.assoc] using hh

#print axioms normalIso
#print axioms adjacentBoundary
#print axioms positive_boundary
end Verification.LocalizedActualTransverse
