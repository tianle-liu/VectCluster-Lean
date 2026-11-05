/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SelectedWittIncidenceInstances
import Verification.OriginalWittCoefficientTerms
import Verification.OriginalWittTensorDifferential
import Verification.OriginalOrderedGradedRow

/-!
# Original Witt Row Comparison

The entire actual ordered coefficient-row differential agrees with the
literal integral Witt complex tensored with the ordinary coefficient group.
-/
noncomputable section
open scoped Classical TensorProduct
set_option quotPrecheck false
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1600000
namespace Verification.OriginalWittRowComparison
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Verification.StrictProjectiveModel Verification.FrozenAcyclicCover
open Verification.ExchangeOpenCover Verification.IndependentChartIndex
open Verification.WittSheafSectionsInput
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



variable (W : Scheme.{0}ᵒᵖ ⥤ CommRingCat.{0}) (WD : Symbols R W)
variable (WT : TorusBasis R W WD) (WH : WittSheafAffineInvariance.Standard R W)
variable (WE : Comparison R W site N)

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

variable (WN : LaurentNormalization R W WD site N WE Cg)
variable (WO : WittThomOrientationInput.Normalization J L G R site M N V O W WD WE)
local notation "TC" => OriginalWittTensorTerms.complex κ n B (RingSection W R) hpos hneg hsupport
local notation "RC" => (fun j : ℤ => StrictCoefficientCochains.complex (Model).complex (M j))
local notation "TE" => OriginalWittCoefficientTerms.termEquiv J L G R T κ n B hpos hneg hsupport hf hs
  E P H empty site M N V W WD WT WH WE
local notation "SE" => OriginalOrderedStrictSections.termEquiv J L G R T κ n B hpos hneg hsupport hf hs
  E P H empty site M N V

include Q hCg Norm WN WO in
theorem differential (p : ℕ) (j : ℤ) (x : (TC).X p) :
    (RC j).d p (p+1) (TE p j x) = TE (p+1) j ((TC).d p (p+1) x) := by
  apply (SE (p+1) j).injective
  funext b
  let v₀ := OriginalOrderedGradedRow.targetVertex κ n B p b
  apply OriginalFiberSectionIso.pullback_injective J L G R κ n b.val B v₀ U
    hpos hneg hsupport b.property.2 (hf b.val b.property.2) (hs b.val b.property.2)
    (p+1) ((Fintype.card_coe b.val).trans b.property.1) site M N V hV j
  rw [OriginalOrderedGradedRow.pulledback_differential J L G R T κ n B hpos hneg hsupport hf hs E P H empty
    site M N V Q K U hV O Cg hCg Norm p b]
  simp_rw [OriginalWittCoefficientTerms.termEquiv_apply]
  simp_rw [OriginalOrderedWittResidue.residue J L G E R κ n B P hpos hneg hsupport hf hs U
    p b _ site M N V hV Cg hCg O W WD WT WH WE WN WO]
  let New := ExchangeTransverseSlice.Fiber (ActualOpenChart.characters R (Selected n b.val)
    (Other n b.val ⊕ κ) (Other n b.val) (matrix κ n b.val B))
  let hsNew : Algebra.Smooth R New := OriginalWittAdjacentMonomialResidue.fiberSmooth R κ n b.val B
    (hf b.val b.property.2) (hs b.val b.property.2)
  have hn := WE.natural (GlobalNormalFrame.ZeroLayer R κ n b.val B) New
    (OriginalASMonomialUnits.smooth R κ n b.val B (hf b.val b.property.2) (hs b.val b.property.2)
      hpos hneg hsupport b.property.2) hsNew
    (OriginalCanonicalFiberProjection.projection R κ n b.val B hpos hneg hsupport b.property.2)
    (j-(p+1 : ℕ))
    (OriginalWittSectionCoordinates.equiv R κ n b.val B (hf b.val b.property.2) (hs b.val b.property.2)
      hpos hneg hsupport b.property.2 W WD WT WH
        (OriginalWittTensorTerms.termEquiv κ n B (RingSection W R) (p+1) ((TC).d p (p+1) x) b))
  refine Eq.trans ?_ hn
  rw [OriginalWittTensorDifferential.apply]
  simp only [map_sum,map_zsmul]
  apply Finset.sum_congr rfl
  intro v _
  congr 1
  exact SelectedWittIncidenceInstances.sign b.val v _

#print axioms differential
end Verification.OriginalWittRowComparison
