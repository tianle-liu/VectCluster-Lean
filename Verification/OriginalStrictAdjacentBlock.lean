/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalStrictBlockSections
import Verification.OriginalActualLaurentResidue

/-!
# Original Strict Adjacent Block

Each literal strict-model local block evaluates to the genuine adjacent residue; all other blocks vanish.
-/
noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
namespace Verification.OriginalStrictAdjacentBlock
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

variable (p : ℕ) (b : ActualCellThom.Index κ n B (p+1)) (v : Selected n b.val)
set_option quotPrecheck false
local notation "New" => ExchangeTransverseSlice.Fiber (ActualOpenChart.characters R (Selected n b.val)
  (Other n b.val ⊕ κ) (Other n b.val) (IndependentChartIndex.matrix κ n b.val B))
local notation "Edge" => ActualGlobalBoundary.edgeIndex κ n B p b v

include hCg in
omit [HasBinaryBiproducts A] [J.Additive] [J.IsTriangulated] [HasFiniteBiproducts D]
  [HasZeroObject D] [Pretriangulated D] [L.IsTriangulated] in
theorem residue_zero (j : ℤ) :
    OriginalOrderedGradedRow.residueValue J L G R κ n B hpos hneg hsupport hf hs E P site M N V U hV O Cg p b v j 0 = 0 := by
  rw [OriginalActualLaurentResidue.residue_formula J L G E R κ n B P hpos hneg hsupport hf hs U
    p b v site M N V hV Cg hCg O]
  simp only [map_zero]

include Q hCg Norm in
theorem adjacent (j : ℤ)
    (f : (StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs p Edge).term ⟶ M j) :
    ActualSheafContractionRestriction.pullback site (N (j-(p+1 : ℕ)))
      (OriginalCanonicalFiberProjection.projection R κ n b.val B hpos hneg hsupport b.property.2).toRingHom
      (OriginalOrderedStrictSections.localEquiv J L G R κ n B hpos hneg hsupport hf hs site M N V (p+1) j b
        (StrictCellTests.testAddEquiv J (StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs (p+1) b) (M j)
          (OriginalStrictLocalBlocks.block J L G R T κ n B hpos hneg hsupport hf hs E P H empty p b Edge ≫ f))) =
    OriginalOrderedGradedRow.residueValue J L G R κ n B hpos hneg hsupport hf hs E P site M N V U hV O Cg p b v j
      (OriginalOrderedStrictSections.localEquiv J L G R κ n B hpos hneg hsupport hf hs site M N V p j Edge
        (StrictCellTests.testAddEquiv J (StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs p Edge) (M j) f)) := by
  have h := OriginalOrderedGradedRow.pulledback_differential J L G R T κ n B hpos hneg hsupport hf hs E P H empty site M N V
    Q K U hV O Cg hCg Norm p b j (OriginalStrictLocalBlocks.coefficient J L G R T κ n B hpos hneg hsupport hf hs E P H empty (M j) p Edge f)
  rw [OriginalStrictBlockSections.differential] at h
  refine h.trans ?_
  rw [Finset.sum_eq_single v]
  · rw [OriginalStrictBlockSections.coefficient_self]
  · intro w _ hw
    rw [OriginalStrictBlockSections.coefficient_other J L G R T κ n B hpos hneg hsupport hf hs E P H empty site M N V p j Edge
      (ActualGlobalBoundary.edgeIndex κ n B p b w)
      (fun hh => hw (OriginalStrictBlockSections.edge_injective κ n B p b hh))]
    exact residue_zero J L G R κ n B hpos hneg hsupport hf hs E P site M N V U hV O Cg hCg p b w j
  · simp only [Finset.mem_univ,not_true_eq_false,IsEmpty.forall_iff]

include Q hCg Norm O in
theorem nonadjacent (j : ℤ) (i : ActualCellThom.Index κ n B p)
    (hi : ∀ w : Selected n b.val, ActualGlobalBoundary.edgeIndex κ n B p b w ≠ i)
    (f : (StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs p i).term ⟶ M j) :
    ActualSheafContractionRestriction.pullback site (N (j-(p+1 : ℕ)))
      (OriginalCanonicalFiberProjection.projection R κ n b.val B hpos hneg hsupport b.property.2).toRingHom
      (OriginalOrderedStrictSections.localEquiv J L G R κ n B hpos hneg hsupport hf hs site M N V (p+1) j b
        (StrictCellTests.testAddEquiv J (StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs (p+1) b) (M j)
          (OriginalStrictLocalBlocks.block J L G R T κ n B hpos hneg hsupport hf hs E P H empty p b i ≫ f))) = 0 := by
  have h := OriginalOrderedGradedRow.pulledback_differential J L G R T κ n B hpos hneg hsupport hf hs E P H empty site M N V
    Q K U hV O Cg hCg Norm p b j (OriginalStrictLocalBlocks.coefficient J L G R T κ n B hpos hneg hsupport hf hs E P H empty (M j) p i f)
  rw [OriginalStrictBlockSections.differential] at h
  refine h.trans (Finset.sum_eq_zero ?_)
  intro w _
  rw [OriginalStrictBlockSections.coefficient_other J L G R T κ n B hpos hneg hsupport hf hs E P H empty site M N V p j i
    (ActualGlobalBoundary.edgeIndex κ n B p b w) (hi w)]
  exact residue_zero J L G R κ n B hpos hneg hsupport hf hs E P site M N V U hV O Cg hCg p b w j

#print axioms residue_zero
#print axioms adjacent
#print axioms nonadjacent
end Verification.OriginalStrictAdjacentBlock
