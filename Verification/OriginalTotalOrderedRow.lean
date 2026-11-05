/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalTotalAdjacentResidue

/-!
# Original Total Ordered Row

The complete genuine ordered Gysin row in total graded MW sections.
The sum is over the actual selected vertices and uses the constructed
original source maps, with the ordinary quadratic Thom action.
-/
noncomputable section
set_option quotPrecheck false
namespace Verification.OriginalTotalOrderedRow
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open Verification.StrictProjectiveModel Verification.FrozenAcyclicCover
open Verification.ExchangeOpenCover Verification.IndependentChartIndex
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasBinaryBiproducts A]
variable [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
variable [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [HasFiniteBiproducts D]
variable (J : DerivedCategory A ⥤ D) [J.Additive] [J.CommShift ℤ] [J.IsTriangulated]
variable (L : DerivedCategory C ⥤ D) [L.Additive] [L.CommShift ℤ] [L.IsTriangulated]
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (R : Type) [CommRing R]

variable (T : StrictLocalizedCells.TorusCells J L G R)
variable [Nontrivial R] (κ : Type) [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hf : ∀ I, Independent (laterWeights κ n B) I →
  Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (hs : ∀ I, Independent (laterWeights κ n B) I →
  FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)))

variable (E : OpenConeExcision.StandardExcision G) (P : LocalizedCoordinatePurity.Standard L R G)

variable (H : ChainRepresentability (A := A))
variable (empty : ∀ X : Scheme, IsEmpty X → IsZero (L.obj (DerivedCategory.Q.obj (G.obj X))))

variable (site : GrothendieckTopology Scheme.{0})
variable (M : ℤ → A) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (V : LocalizedThomSections.Standard J L G R site M N)

open scoped BigOperators
local notation "Model" => OriginalPositiveCellular.model J L G R T κ n B hpos hneg hsupport hf hs E P H empty


variable (Q : LocalizedIndexedPurity.Standard L R G P)
variable (K : LocalizedNormalizedFlag.Standard L R G E P)
variable (U : LocalizedAffineThomInvariance.Standard L R G)


variable (hV : LocalizedThomSections.Naturality J L G R site M N V)
variable (O : ThomPermutationInput.Standard J L G R site M N V)
variable (Cg : StandardThomContractionNormalization.Grading R site N)
variable (hCg : SheafContractionNaturality.Standard R site N Cg)
variable (Norm : ∀ (ι : Type) [Fintype ι] [LinearOrder ι] [DecidableEq ι] (v : ι) (r : ℕ)
  (hr : Fintype.card (CoordinateFlag.Old ι v) = r),
  StandardThomContractionNormalization.Standard J L G R site M N V hV U
    (CoordinateFlag.Old ι v) r hr (K.principal ι v) Cg)
variable (p : ℕ) (b : ActualCellThom.Index κ n B (p+1))
set_option quotPrecheck false
local notation "Sel" => Selected n b.val
local notation "Rest" => Other n b.val
local notation "Mat" => IndependentChartIndex.matrix κ n b.val B

local notation "New" => ExchangeTransverseSlice.Fiber (ActualOpenChart.characters R Sel (Rest ⊕ κ) Rest Mat)
local notation "hMat" => IndependentChartIndex.matrix_zero_block κ n b.val B hpos hneg hsupport b.property.2
variable (W : GradedMilnorWittSheaf.Standard site N)
variable (QO : GradedMilnorWittThomOrientation.Normalization J L G R site M N V O W)
open Verification.GradedSectionTotal

include Q hCg Norm QO in
theorem row (j : ℤ)
    (a : (StrictCoefficientCochains.complex (Model).complex (M j)).X p) :
    includeDegree (W.grading (CommRingCat.of New)) (j-(p+1 : ℕ))
      (ActualSheafContractionRestriction.pullback site (N (j-(p+1 : ℕ)))
        (OriginalCanonicalFiberProjection.projection R κ n b.val B hpos hneg hsupport b.property.2).toRingHom
        (OriginalOrderedStrictSections.termEquiv J L G R T κ n B hpos hneg hsupport hf hs E P H empty
          site M N V (p+1) j ((StrictCoefficientCochains.complex (Model).complex (M j)).d p (p+1) a) b))=
    ∑ v : b.val, (W.symbols (CommRingCat.of New)).g^
      ((Finset.univ.erase v).filter (fun i : Sel => i<v)).card *
      GradedMilnorWittLaurent.residue R site N W Cg New
        (ActualTransversePairSmooth.pair_smooth_AS R Sel (Rest ⊕ κ) Rest Sum.inl Mat hMat
          (hf b.val b.property.2) (hs b.val b.property.2) v).1
        (GradedMilnorWittSheaf.pullback site N W
          (S:=CommRingCat.of (GlobalNormalFrame.ZeroLayer R κ n
            (ActualGlobalBoundary.edgeIndex κ n B p b v).val B))
          (T:=CommRingCat.of (LaurentBasepoint.Laurent New))
          (OriginalActualLaurentResidue.sourceMap R κ n B hpos hneg hsupport p b v).toRingHom
          (includeDegree (W.grading (CommRingCat.of (GlobalNormalFrame.ZeroLayer R κ n
            (ActualGlobalBoundary.edgeIndex κ n B p b v).val B))) (j-p)
            (OriginalOrderedStrictSections.termEquiv J L G R T κ n B hpos hneg hsupport hf hs E P H empty
              site M N V p j a (ActualGlobalBoundary.edgeIndex κ n B p b v)))) := by
  rw [OriginalOrderedGradedRow.pulledback_differential J L G R T κ n B hpos hneg hsupport hf hs
    E P H empty site M N V Q K U hV O Cg hCg Norm p b,map_sum]
  apply Finset.sum_congr rfl
  intro v _
  exact OriginalTotalAdjacentResidue.total_residue J L G E R κ n B P hpos hneg hsupport hf hs U
    p b v site M N V hV Cg hCg O W QO j _

#print axioms row
end Verification.OriginalTotalOrderedRow
