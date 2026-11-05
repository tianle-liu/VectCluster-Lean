/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalStrictContractionBlocks

/-!
# Original Source Transport Cancellation

The original source transport cancels its intermediate purity
comparison. The remaining morphism is built only from actual ring
coordinate maps, affine relative cones, and the old normal reindexing.
-/
noncomputable section
set_option quotPrecheck false
set_option synthInstance.maxHeartbeats 100000
namespace Verification.OriginalSourceTransportCancellation
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.ExchangeOpenCover Verification.IndependentBasicOpen
open Verification.IndependentOpenCoordinates Verification.GlobalExchangeSmooth
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable {Z : Type*} [Category Z] [Preadditive Z] [HasFiniteBiproducts Z]
variable [HasZeroObject Z] [HasShift Z ℤ] [∀ q : ℤ, (CategoryTheory.shiftFunctor Z q).Additive] [Pretriangulated Z]
variable (L : DerivedCategory C ⥤ Z) [L.Additive] [L.CommShift ℤ] [L.IsTriangulated]
variable (G : Scheme ⥤ CochainComplex C ℤ) (E : OpenConeExcision.StandardExcision G)
variable (R κ : Type) [CommRing R] [Nontrivial R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (P : LocalizedCoordinatePurity.Standard L R G)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hf : ∀ I, Independent (laterWeights κ n B) I → Function.Injective (selectedMap κ n B I))
variable (hs : ∀ I, Independent (laterWeights κ n B) I →
  FreezingLattice.Saturated (LinearMap.range (selectedMap κ n B I)))
variable (N : LocalizedIndexedPurity.Standard L R G P)
variable (K : LocalizedNormalizedFlag.Standard L R G E P)
variable (H : LocalizedAffineThomInvariance.Standard L R G)
variable (p : ℕ) (J : ActualCellThom.Index κ n B (p+1)) (v : Selected n J.val)
local notation "W" => BasicOpen R κ n J.val B
local notation "Sel" => Selected n J.val
local notation "x" => selectedCoordinate R κ n J.val B
local notation "Rest" => Other n J.val
local notation "D" => matrix κ n J.val B
local notation "F" => AffineRelativeThom.theory R (CoordinateFlag.Old (Selected n J.val) v) G
local notation "S" => ActualAdjacentTorusBoundary.shiftedTheory R F ⋙ L
local notation "I" => ActualGlobalBoundary.edgeIndex κ n B p J v
local notation "O" => ActualTransverseLocalization.OpenSource R Sel (Rest ⊕ κ) Rest Sum.inl D v
local notation "OldT" => ActualTorusFace.OldTorus R Sel (Rest ⊕ κ) Rest D v
local notation "oldFrame" => ActualIndexedPurity.sourceFrame R κ n B p J v hpos hneg hsupport hf hs
local notation "o" => LocalizedActualFlag.oldIso L R κ n J.val B v G E P hpos hneg hsupport
  J.property.2 (hf J.val J.property.2) (hs J.val J.property.2)
local notation "a" => (LocalizedFlagPairs.oldComparison L R W Sel x v G E P oldFrame).hom ≫
  L.map (ActualIndexedPurity.normalTransport R κ n B G p J v)
local notation "full" => P.comparison W Sel x (IndependentCoordinatePurity.frame R κ n J.val B
  hpos hneg hsupport J.property.2 (hf J.val J.property.2) (hs J.val J.property.2))
local notation "torusOld" => OriginalLocalizedTorusContraction.oldIso L R κ n J.val B v G H
  hpos hneg hsupport J.property.2 (hf J.val J.property.2) (hs J.val J.property.2)
local notation "torusNew" => OriginalLocalizedTorusContraction.torusNormalIso L R κ n J.val B v G H
  hpos hneg hsupport J.property.2 (hf J.val J.property.2) (hs J.val J.property.2)
local notation "thomNew" => OriginalLocalizedTorusContraction.fiberThomIso L R κ n J.val B v G E P K H
  hpos hneg hsupport J.property.2 (hf J.val J.property.2) (hs J.val J.property.2)
local notation "adj" => LocalizedActualTransverse.adjacentBoundary L R κ n J.val B v G E P K
  hpos hneg hsupport J.property.2 (hf J.val J.property.2) (hs J.val J.property.2)
local notation "normal" => LocalizedActualTransverse.normalIso L R κ n J.val B v G


local notation "Q₁" => CoordinateLocalizationPair.OpenRing W Sel x v ⧸
  ConormalFrame.ideal (CoordinateLocalizationPair.coordinate W Sel x v)
local notation "e" => (F).mapIso (ActualCoordinateFlag.openEquiv R κ n J.val B v).toUnder.op

def geometric : (DerivedCategory.Q ⋙ L).obj
    ((F).obj (op (CommRingCat.mkUnder (CommRingCat.of R) O))) ⟶
    L.obj (ActualCellThom.localThom G R κ n B p I) :=
  (DerivedCategory.Q ⋙ L).map (e).hom ≫
    L.map (DerivedCategory.Q.map (RelativeFlagOpenBoundary.coefficientIso R W Sel x v G).hom) ≫
    L.map (RelativeProductConeNaturality.derivedIso R Q₁ (CoordinateFlag.Old Sel v) G).hom ≫
    L.map (ActualIndexedPurity.normalTransport R κ n B G p J v)

omit [HasFiniteBiproducts Z] [HasZeroObject Z] [∀ q : ℤ, (CategoryTheory.shiftFunctor Z q).Additive]
  [Pretriangulated Z] [L.IsTriangulated] [L.CommShift ℤ] [HasShift Z ℤ] [Preadditive Z] [L.Additive] in
theorem old_comparison_cancel : (o).inv ≫ (a) =
    L.map (DerivedCategory.Q.map (RelativeFlagOpenBoundary.coefficientIso R W Sel x v G).hom) ≫
    L.map (RelativeProductConeNaturality.derivedIso R Q₁ (CoordinateFlag.Old Sel v) G).hom ≫
    L.map (ActualIndexedPurity.normalTransport R κ n B G p J v) := by
  simp only [ActualIndexedPurity.sourceFrame, LocalizedActualFlag.oldIso, LocalizedFlagPairs.oldIso, Iso.trans_inv,
    Iso.symm_inv, Functor.mapIso_hom, Category.assoc, Iso.inv_hom_id_assoc]

omit [HasFiniteBiproducts Z] [HasZeroObject Z] [∀ q : ℤ, (CategoryTheory.shiftFunctor Z q).Additive]
  [Pretriangulated Z] [L.IsTriangulated] [Preadditive Z] [L.Additive] in
set_option maxHeartbeats 800000 in
theorem transport_eq : OriginalStrictContractionBlocks.sourceTransport L G E R κ n B P
    hpos hneg hsupport hf hs p J v =
    ((DerivedCategory.Q ⋙ L).commShiftIso (1 : ℤ)).hom.app
      ((F).obj (op (CommRingCat.mkUnder (CommRingCat.of R) O))) ≫
      (geometric L G R κ n B p J v)⟦(1 : ℤ)⟧' := by
  let m := L.map (DerivedCategory.Q.map (RelativeFlagOpenBoundary.coefficientIso R W Sel x v G).hom) ≫
    L.map (RelativeProductConeNaturality.derivedIso R Q₁ (CoordinateFlag.Old Sel v) G).hom ≫
    L.map (ActualIndexedPurity.normalTransport R κ n B G p J v)
  have hc : (o).inv⟦(1 : ℤ)⟧' ≫ (a)⟦(1 : ℤ)⟧' = m⟦(1 : ℤ)⟧' := by
    rw [← CategoryTheory.Functor.map_comp]
    exact congrArg (fun f => f⟦(1 : ℤ)⟧')
      (old_comparison_cancel L G E R κ n B P hpos hneg hsupport hf hs p J v)
  have hn := ((DerivedCategory.Q ⋙ L).commShiftIso (1 : ℤ)).hom.naturality (e).hom
  change (DerivedCategory.Q ⋙ L).map ((e).hom⟦(1 : ℤ)⟧') ≫
      ((DerivedCategory.Q ⋙ L).commShiftIso (1 : ℤ)).hom.app _ =
    ((DerivedCategory.Q ⋙ L).commShiftIso (1 : ℤ)).hom.app _ ≫
      ((DerivedCategory.Q ⋙ L).map (e).hom)⟦(1 : ℤ)⟧' at hn
  simp only [OriginalStrictContractionBlocks.sourceTransport, OriginalStrictContractionBlocks.openIso,
    LocalizedFlagCoherence.shiftedIso, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
    Functor.mapIso_hom, ← Iso.app_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [hc]
  change (DerivedCategory.Q ⋙ L).map ((e).hom⟦(1 : ℤ)⟧') ≫
      ((DerivedCategory.Q ⋙ L).commShiftIso (1 : ℤ)).hom.app _ ≫ m⟦(1 : ℤ)⟧' = _
  rw [← Category.assoc, hn, Category.assoc, ← CategoryTheory.Functor.map_comp]
  rfl


#print axioms geometric
#print axioms old_comparison_cancel
#print axioms transport_eq
end Verification.OriginalSourceTransportCancellation
