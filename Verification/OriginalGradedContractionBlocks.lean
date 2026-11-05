/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualGradedContractionBoundary
import Verification.OriginalStrictContractionBlocks

/-!
# Original Graded Contraction Blocks

The original positive differential block, evaluated in its actual
new-first torus coordinates, is genuine coefficient contraction at u=1
followed by the actual character-fiber pullback. All chart and source
transports are the existing maps from the original filtration.
-/
noncomputable section
set_option quotPrecheck false
set_option synthInstance.maxHeartbeats 100000
namespace Verification.OriginalGradedContractionBlocks
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.ExchangeOpenCover Verification.IndependentBasicOpen
open Verification.IndependentOpenCoordinates Verification.GlobalExchangeSmooth
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {Z : Type*} [Category Z] [Preadditive Z] [HasFiniteBiproducts Z]
variable [HasZeroObject Z] [HasShift Z ℤ] [∀ q : ℤ, (CategoryTheory.shiftFunctor Z q).Additive] [Pretriangulated Z]
variable (J : DerivedCategory A ⥤ Z) [J.Additive] [J.CommShift ℤ]
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
variable (Q : LocalizedIndexedPurity.Standard L R G P)
variable (K : LocalizedNormalizedFlag.Standard L R G E P)
variable (H : LocalizedAffineThomInvariance.Standard L R G)
variable (p : ℕ) (t : ActualCellThom.Index κ n B (p+1)) (v : Selected n t.val)
local notation "Sel" => Selected n t.val
local notation "Rest" => Other n t.val
local notation "D" => matrix κ n t.val B
local notation "μ" => CoordinateFlag.Old (Selected n t.val) v
local notation "F" => AffineRelativeThom.theory R μ G
local notation "S" => ActualAdjacentTorusBoundary.shiftedTheory R F ⋙ L
local notation "I" => ActualGlobalBoundary.edgeIndex κ n B p t v
local notation "Old" => ActualTorusReducedRestriction.OldBase R Sel (Rest ⊕ κ) Rest D v
local notation "New" => ExchangeTransverseSlice.Fiber (ActualOpenChart.characters R Sel (Rest ⊕ κ) Rest D)
local notation "hD" => matrix_zero_block κ n t.val B hpos hneg hsupport t.property.2
local notation "hsNew" => (ActualTransversePairSmooth.pair_smooth_AS R Sel (Rest ⊕ κ) Rest Sum.inl D hD
  (hf t.val t.property.2) (hs t.val t.property.2) v).1
local notation "hsOld" => ActualOldFiberSmooth.old_smooth R Sel (Rest ⊕ κ) Rest D v Sum.inl hD
  (hf t.val t.property.2) (hs t.val t.property.2)
local notation "torusOld" => OriginalLocalizedTorusContraction.oldIso L R κ n t.val B v G H
  hpos hneg hsupport t.property.2 (hf t.val t.property.2) (hs t.val t.property.2)
local notation "torusNew" => OriginalLocalizedTorusContraction.torusNormalIso L R κ n t.val B v G H
  hpos hneg hsupport t.property.2 (hf t.val t.property.2) (hs t.val t.property.2)

omit [Fintype κ] in
theorem old_card : Fintype.card μ = p := by
  rw [Fintype.card_congr (AdjacentCoordinatePair.indexEquiv n t.val v)]
  change Fintype.card ↥(t.val.erase v.val) = p
  rw [Fintype.card_coe]
  exact (I).property.1

variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (hV : LocalizedThomSections.Naturality J L G R site M N V)
variable (Cg : StandardThomContractionNormalization.Grading R site N)
variable (hCg : SheafContractionNaturality.Standard R site N Cg)
variable (Norm : StandardThomContractionNormalization.Standard J L G R site M N V hV H
  (CoordinateFlag.Old (Selected n t.val) v) p (old_card κ n B p t v)
  (LocalizedActualFlag.principal L R n t.val v G E P K) Cg)
variable (j : ℤ)
local notation "Coef" => J.obj (DerivedCategory.Q.obj (StrictSingleModel.single (-((p+1 : ℕ) : ℤ)) (M j)))
local instance optionOrder : LinearOrder (Option μ) := inferInstanceAs (LinearOrder (WithBot μ))

def oldKernel
    (b : (L.obj (ActualCellThom.localThom G R κ n B p I))⟦(1 : ℤ)⟧ ⟶ Coef) :
    (AffineSheafContraction.sheafAtOne R Old site N (j-p)).ker :=
  ActualContractionSectionNaturality.oldEquiv J L G R Sel (Rest ⊕ κ) Rest Sum.inl D hD v
    (hf t.val t.property.2) (hs t.val t.property.2) μ p (old_card κ n B p t v) site M N V hV j
    (LocalizedTorusContraction.oldContraction R Sel (Rest ⊕ κ) Rest D v L F Coef
      ((torusOld).hom ≫ OriginalStrictContractionBlocks.sourceTransport L G E R κ n B P
        hpos hneg hsupport hf hs p t v ≫ b))

include Q K hCg Norm in
omit [J.Additive] in
theorem block_evaluation
    (b : (L.obj (ActualCellThom.localThom G R κ n B p I))⟦(1 : ℤ)⟧ ⟶ Coef) :
    AffineShiftedThomSections.evaluate J L G R New (Option μ) (p+1)
      (by simp only [Fintype.card_option, old_card κ n B p t v]) site M N V hsNew j
      ((torusNew).inv ≫ OriginalStrictBoundaryGeometry.positiveBlock L G E R κ n B P
        hpos hneg hsupport hf hs p t I ≫ b) =
    ActualSheafContractionRestriction.pullback site (N (j-(p+1 : ℕ)))
      (ActualTorusReducedRestriction.fiberRestriction R Sel (Rest ⊕ κ) Rest D v).toRingHom
      (StandardThomContractionNormalization.lower R site N Cg Old hsOld p j
        (oldKernel J L G E R κ n B P hpos hneg hsupport hf hs H p t v site M N V hV j b)) := by
  rw [OriginalStrictContractionBlocks.positive_on_sections L G E R κ n B P
    hpos hneg hsupport hf hs Q K H p t v Coef b]
  simp only [Iso.inv_hom_id_assoc]
  exact ActualGradedContractionBoundary.boundary_evaluation J L G R Sel (Rest ⊕ κ) Rest
    Sum.inl D hD v (hf t.val t.property.2) (hs t.val t.property.2) μ p (old_card κ n B p t v)
    site M N V hV H (LocalizedActualFlag.principal L R n t.val v G E P K) Cg hCg Norm j _

#print axioms old_card
#print axioms optionOrder
#print axioms oldKernel
#print axioms block_evaluation
end Verification.OriginalGradedContractionBlocks
