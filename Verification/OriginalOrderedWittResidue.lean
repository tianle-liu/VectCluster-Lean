/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalActualLaurentResidue
import Verification.OriginalWittAdjacentFace
import Verification.WittSectionResidueTransport
import Verification.WittThomOrientationInput

/-!
# Original Ordered Witt Residue

The actual ordered sheaf-row adjacent block is the literal integral
Witt face tensored with ordinary Witt coefficients, with the genuine Thom
orientation supplying its alternating sign.
-/
noncomputable section
open scoped TensorProduct
set_option quotPrecheck false
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1600000
namespace Verification.OriginalOrderedWittResidue
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.ExchangeOpenCover Verification.IndependentBasicOpen
open Verification.IndependentOpenCoordinates Verification.GlobalExchangeSmooth
open Verification.WittSheafSectionsInput
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

variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (hV : LocalizedThomSections.Naturality J L G R site M N V)


variable (Cg : StandardThomContractionNormalization.Grading R site N)
variable (hCg : SheafContractionNaturality.Standard R site N Cg)
variable (O : ThomPermutationInput.Standard J L G R site M N V)


variable (W : Scheme.{0}ᵒᵖ ⥤ CommRingCat.{0}) (WD : Symbols R W)
variable (WT : TorusBasis R W WD) (WH : WittSheafAffineInvariance.Standard R W)
variable (WE : Comparison R W site N)
variable (WN : LaurentNormalization R W WD site N WE Cg)
variable (WO : WittThomOrientationInput.Normalization J L G R site M N V O W WD WE)
local notation "hsSource" => OriginalASMonomialUnits.smooth R κ n (I).val B (hf (I).val (I).property.2)
  (hs (I).val (I).property.2) hpos hneg hsupport (I).property.2
local notation "eqSource" => OriginalWittSectionCoordinates.equiv R κ n (I).val B (hf (I).val (I).property.2)
  (hs (I).val (I).property.2) hpos hneg hsupport (I).property.2 W WD WT WH
local notation "eqTarget" => OriginalWittSectionCoordinates.equiv R κ n t.val B (hf t.val t.property.2)
  (hs t.val t.property.2) hpos hneg hsupport t.property.2 W WD WT WH
local notation "proj" => OriginalCanonicalFiberProjection.projection R κ n t.val B hpos hneg hsupport t.property.2

include hCg WN WO in
omit [HasFiniteBiproducts Z] [HasZeroObject Z] [Pretriangulated Z] [J.Additive] [L.IsTriangulated] in
theorem residue (j : ℤ)
    (a : OriginalWittQuotient.Stratum (fun a i => B a (Sum.inl i))
      (ActualGlobalBoundary.edgeIndex κ n B p t v).val ⊗[ℤ] RingSection W R) :
    OriginalOrderedGradedRow.residueValue J L G R κ n B hpos hneg hsupport hf hs E P
      site M N V H hV O Cg p t v j (WE.sections _ hsSource (j-p) (eqSource a)) =
      WE.sections New hsNew (j-(p+1 : ℕ))
        (((-1 : ℤ)^((Finset.univ.erase v).filter (fun i : Sel => i<v)).card) •
          pullback W (proj).toRingHom
            (eqTarget (OriginalWittAdjacentFace.integerFace κ n t.val B v hpos hneg hsupport t.property.2
              (RingSection W R) a))) := by
  rw [OriginalActualLaurentResidue.residue_formula J L G E R κ n B P hpos hneg hsupport hf hs H
    p t v site M N V hV Cg hCg O]
  rw [WittSectionResidueTransport.pullback_residue R W site N WE Cg New hsNew hsSource
    (OriginalActualLaurentResidue.sourceMap R κ n B hpos hneg hsupport p t v)]
  rw [WittSectionResidueTransport.degreeCast]
  rw [WittThomOrientationInput.orientation_coefficient J L G R site M N V O W WD WE WO New hsNew]
  congr 1
  exact congrArg (fun x => ((-1 : ℤ)^((Finset.univ.erase v).filter (fun i : Sel => i<v)).card) • x)
    (DFunLike.congr_fun (OriginalWittAdjacentFace.comparison R κ n t.val B v hD
      (hf (I).val (I).property.2) (hs (I).val (I).property.2) (hf t.val t.property.2) (hs t.val t.property.2)
      hpos hneg hsupport (I).property.2 t.property.2 W WD WT WH site N WE Cg WN (j-p)) a)

#print axioms residue
end Verification.OriginalOrderedWittResidue
