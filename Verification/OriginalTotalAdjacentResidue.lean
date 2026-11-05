/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalActualLaurentResidue
import Verification.GradedMilnorWittThomOrientation
import Verification.GradedMilnorWittLaurent

/-!
# Original Total Adjacent Residue

Total graded version of the genuine adjacent geometric row. The only
extra normalization is the ordinary quadratic Thom action, uniformly over
all smooth coefficient schemes.
-/
noncomputable section
set_option quotPrecheck false
namespace Verification.OriginalTotalAdjacentResidue
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
variable (H : LocalizedAffineThomInvariance.Standard L R G)
variable (p : ℕ) (t : ActualCellThom.Index κ n B (p+1)) (v : Selected n t.val)
local notation "Sel" => Selected n t.val
local notation "Rest" => Other n t.val
local notation "D" => matrix κ n t.val B
local notation "μ" => CoordinateFlag.Old (Selected n t.val) v
local notation "F" => AffineRelativeThom.theory R μ G
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

open Verification.SheafGradedLaurentResidue Verification.GradedSectionTotal
variable (W : GradedMilnorWittSheaf.Standard site N)
variable (QO : GradedMilnorWittThomOrientation.Normalization J L G R site M N V O W)

include hCg QO in
omit [HasFiniteBiproducts Z] [HasZeroObject Z] [Pretriangulated Z] [L.IsTriangulated] [J.Additive] in
theorem total_residue (j : ℤ)
    (a : Section site N (GlobalNormalFrame.ZeroLayer R κ n (I).val B) (j-p)) :
    includeDegree (W.grading (CommRingCat.of New)) (j-(p+1 : ℕ))
      (OriginalOrderedGradedRow.residueValue J L G R κ n B hpos hneg hsupport hf hs E P
        site M N V H hV O Cg p t v j a)=
    (W.symbols (CommRingCat.of New)).g^
      ((Finset.univ.erase v).filter (fun i : Sel => i<v)).card *
      GradedMilnorWittLaurent.residue R site N W Cg New hsNew
        (GradedMilnorWittSheaf.pullback site N W
          (S:=CommRingCat.of (GlobalNormalFrame.ZeroLayer R κ n (I).val B))
          (T:=CommRingCat.of (LaurentBasepoint.Laurent New))
          (OriginalActualLaurentResidue.sourceMap R κ n B hpos hneg hsupport p t v).toRingHom
          (includeDegree (W.grading (CommRingCat.of
            (GlobalNormalFrame.ZeroLayer R κ n (I).val B))) (j-p) a)) := by
  rw [OriginalActualLaurentResidue.residue_formula J L G E R κ n B P hpos hneg hsupport hf hs H
    p t v site M N V hV Cg hCg O]
  rw [GradedMilnorWittThomOrientation.orientation_power J L G R site M N V O W QO New hsNew]
  rw [MilnorWittGradedLaurentNormalization.includeDegree_cast]
  rw [GradedMilnorWittSheaf.pullback_degree]
  rw [GradedMilnorWittLaurent.residue,totalResidue_degree]
  rfl

#print axioms total_residue
end Verification.OriginalTotalAdjacentResidue
