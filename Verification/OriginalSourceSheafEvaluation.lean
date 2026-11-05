/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalSourceTransportCancellation
import Verification.OriginalSourceCoefficientCoordinates
import Verification.OriginalOldNormalNumbering
import Verification.OriginalGradedContractionBlocks
import Verification.OrderedReindexedThomNaturality
import Verification.OriginalOrderedStrictSections

/-!
# Original Source Sheaf Evaluation

The actual source transport acts on ordered coefficient sections by
its explicitly constructed coefficient ring map. The old normal reindexing
is increasing, so its coefficient action has no further permutation.
-/
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
namespace Verification.OriginalSourceSheafEvaluation
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.ExchangeOpenCover Verification.IndependentBasicOpen
open Verification.IndependentOpenCoordinates Verification.GlobalExchangeSmooth
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D]
variable (J : DerivedCategory A ⥤ D) (L : DerivedCategory C ⥤ D)
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (R κ : Type) [CommRing R] [Nontrivial R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j=0 ↔ laterWeights κ n B i j=0)
variable (hf : ∀ I, Independent (laterWeights κ n B) I → Function.Injective (selectedMap κ n B I))
variable (hs : ∀ I, Independent (laterWeights κ n B) I → FreezingLattice.Saturated (LinearMap.range (selectedMap κ n B I)))
variable (p : ℕ) (t : ActualCellThom.Index κ n B (p+1)) (v : Selected n t.val)
local notation "I" => ActualGlobalBoundary.edgeIndex κ n B p t v
local notation "W" => BasicOpen R κ n t.val B
local notation "Sel" => Selected n t.val
local notation "Rest" => Other n t.val
local notation "x" => selectedCoordinate R κ n t.val B
local notation "μ" => CoordinateFlag.Old Sel v
local notation "Mat" => matrix κ n t.val B
local notation "F" => AffineRelativeThom.theory R μ G
local notation "Q₁" => CoordinateLocalizationPair.OpenRing W Sel x v ⧸
  ConormalFrame.ideal (CoordinateLocalizationPair.coordinate W Sel x v)
local notation "OldT" => ActualTorusFace.OldTorus R Sel (Rest ⊕ κ) Rest Mat v
local notation "O" => ActualTransverseLocalization.OpenSource R Sel (Rest ⊕ κ) Rest Sum.inl Mat v
local notation "hD" => matrix_zero_block κ n t.val B hpos hneg hsupport t.property.2
local notation "hQ" => (LocalizedOldCoordinateFrame.frame R κ n t.val B v hpos hneg hsupport
  t.property.2 (hf t.val t.property.2) (hs t.val t.property.2)).closedSmooth
local notation "hSource" => IndependentCoordinatePurity.closed_smooth R κ n (I).val B hpos hneg hsupport
  (I).property.2 (hf (I).val (I).property.2) (hs (I).val (I).property.2)
local notation "hTorus" => ActualOldTorusSmooth.old_smooth R Sel (Rest ⊕ κ) Rest Sum.inl Mat hD v
  (hf t.val t.property.2) (hs t.val t.property.2)

def affineMap : Q₁ →ₐ[R] OldT :=
  (ActualTorusFace.oldZeroSection R Sel (Rest ⊕ κ) Rest Sum.inl Mat hD v).comp
    ((ActualCoordinateFlag.openEquiv R κ n t.val B v).toAlgHom.comp
      (CoordinateFlagLocalization.closedEquiv R W Sel x v).toAlgHom)

def sourceAction : L.obj (DerivedCategory.Q.obj ((F).obj (op (CommRingCat.mkUnder (CommRingCat.of R) OldT)))) ⟶
    L.obj (ActualCellThom.localThom G R κ n B p I) :=
  (DerivedCategory.Q ⋙ L).map ((F).map
    (ActualTorusFace.oldZeroSection R Sel (Rest ⊕ κ) Rest Sum.inl Mat hD v).toUnder.op) ≫
      OriginalSourceTransportCancellation.geometric L G R κ n B p t v

omit [Nontrivial R] [Preadditive D] in
theorem sourceAction_eq : sourceAction L G R κ n B hpos hneg hsupport p t v =
    (DerivedCategory.Q ⋙ L).map ((F).map (affineMap R κ n B hpos hneg hsupport p t v).toUnder.op) ≫
      (AffineShiftedThomSections.affineIso L G R Q₁ μ).hom ≫
        L.map (ActualIndexedPurity.normalTransport R κ n B G p t v) := by
  change (DerivedCategory.Q ⋙ L).map ((F).map
      (ActualTorusFace.oldZeroSection R Sel (Rest ⊕ κ) Rest Sum.inl Mat hD v).toUnder.op) ≫
    ((DerivedCategory.Q ⋙ L).map ((F).map (ActualCoordinateFlag.openEquiv R κ n t.val B v).toAlgHom.toUnder.op) ≫
      ((DerivedCategory.Q ⋙ L).map ((F).map (CoordinateFlagLocalization.closedEquiv R W Sel x v).toAlgHom.toUnder.op) ≫
        ((AffineShiftedThomSections.affineIso L G R Q₁ μ).hom ≫
          L.map (ActualIndexedPurity.normalTransport R κ n B G p t v)))) = _
  simp only [← Category.assoc,← Functor.map_comp]
  rfl

variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (hV : LocalizedThomSections.Naturality J L G R site M N V)
variable (j : ℤ)
local notation "Coef" => J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-(p : ℤ)) (M j)))

include hV in
theorem normal_evaluation (a : L.obj (ActualCellThom.localThom G R κ n B p I) ⟶ Coef) :
    OrderedThomSections.evaluate μ p (OriginalGradedContractionBlocks.old_card κ n B p t v) Q₁
      J L G R site M N V hQ j (L.map (ActualIndexedPurity.normalTransport R κ n B G p t v) ≫ a) =
    (N (j-p)).val.map (Spec.map (CommRingCat.ofHom
      (OriginalSourceCoefficientCoordinates.quotientMap R κ n t.val B v).toRingHom)).op
      (OriginalOrderedStrictSections.localEquiv J L G R κ n B hpos hneg hsupport hf hs site M N V p j I a) := by
  change OrderedThomSections.evaluate μ p _ Q₁ J L G R site M N V hQ j
    (L.map (ReindexedThomMap.map (AdjacentCoordinatePair.indexEquiv n t.val v)
      (OriginalSourceCoefficientCoordinates.quotientMap R κ n t.val B v).toRingHom G) ≫ a) = _
  exact OrderedReindexedThomNaturality.evaluate_naturality (Selected n (I).val) μ p
    ((Fintype.card_coe (I).val).trans (I).property.1) (OriginalGradedContractionBlocks.old_card κ n B p t v)
    (AdjacentCoordinatePair.indexEquiv n t.val v)
    (OriginalOldNormalNumbering.numbering n t.val v p _ _) J L G R site M N V hV
    (OriginalSourceCoefficientCoordinates.quotientMap R κ n t.val B v) hSource hQ j a

include hV in
theorem source_evaluation (a : L.obj (ActualCellThom.localThom G R κ n B p I) ⟶ Coef) :
    AffineShiftedThomSections.evaluate J L G R OldT μ p (OriginalGradedContractionBlocks.old_card κ n B p t v)
      site M N V hTorus j (sourceAction L G R κ n B hpos hneg hsupport p t v ≫ a) =
    (N (j-p)).val.map (Spec.map (CommRingCat.ofHom
      (OriginalSourceCoefficientCoordinates.torusMap R κ n t.val B v hD).toRingHom)).op
      (OriginalOrderedStrictSections.localEquiv J L G R κ n B hpos hneg hsupport hf hs site M N V p j I a) := by
  rw [sourceAction_eq,Category.assoc]
  rw [AffineShiftedThomNaturality.evaluate_naturality J L G R Q₁ OldT μ p
    (OriginalGradedContractionBlocks.old_card κ n B p t v)
    (affineMap R κ n B hpos hneg hsupport p t v) site M N V hV hQ hTorus j]
  rw [Category.assoc]
  change (N (j-p)).val.map (Spec.map (CommRingCat.ofHom
    (affineMap R κ n B hpos hneg hsupport p t v).toRingHom)).op
    (OrderedThomSections.evaluate μ p _ Q₁ J L G R site M N V hQ j
      ((AffineShiftedThomSections.affineIso L G R Q₁ μ).inv ≫
        ((AffineShiftedThomSections.affineIso L G R Q₁ μ).hom ≫
          L.map (ActualIndexedPurity.normalTransport R κ n B G p t v) ≫ a))) = _
  rw [Iso.inv_hom_id_assoc,normal_evaluation J L G R κ n B hpos hneg hsupport hf hs p t v site M N V hV j]
  change ActualSheafContractionRestriction.pullback site (N (j-p))
    (affineMap R κ n B hpos hneg hsupport p t v).toRingHom
    (ActualSheafContractionRestriction.pullback site (N (j-p))
      (OriginalSourceCoefficientCoordinates.quotientMap R κ n t.val B v).toRingHom _) = _
  rw [← AddMonoidHom.comp_apply,← ActualSheafContractionRestriction.pullback_comp]
  rfl

#print axioms affineMap
#print axioms sourceAction
#print axioms sourceAction_eq
#print axioms normal_evaluation
#print axioms source_evaluation
end Verification.OriginalSourceSheafEvaluation
