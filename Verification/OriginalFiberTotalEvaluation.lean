/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalFiberProjectionDetection

/-!
# Original Fiber Total Evaluation

The actual fiber evaluation is additive, so its projection tests can be assembled over finite sums of scalar arrows.
-/
noncomputable section
set_option quotPrecheck false
namespace Verification.OriginalFiberTotalEvaluation
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.StrictSingleModel Verification.FrozenAcyclicCover
open Verification.ExchangeOpenCover Verification.IndependentChartIndex
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasFiniteBiproducts D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable (L : DerivedCategory C ⥤ D) [L.Additive]
variable (G : Scheme ⥤ CochainComplex C ℤ) (R : Type) [CommRing R]
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
variable (r : ℕ) (i : ActualCellThom.Index κ n B r)
variable (site : GrothendieckTopology Scheme.{0}) (M : ℤ → A)
variable (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (W : GradedMilnorWittSheaf.Standard site N)
local notation "Base" => GlobalNormalFrame.ZeroLayer R κ n i.val B
local notation "LocalCell" => StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs r i
local notation "Smooth" => IndependentCoordinatePurity.closed_smooth R κ n i.val B hpos hneg hsupport i.property.2
  (hf i.val i.property.2) (hs i.val i.property.2)

local notation "New" => ExchangeTransverseSlice.Fiber (ActualOpenChart.characters R (Selected n i.val)
  (Other n i.val ⊕ κ) (Other n i.val) (IndependentChartIndex.matrix κ n i.val B))
local notation "Projection" => OriginalCanonicalFiberProjection.projection R κ n i.val B hpos hneg hsupport i.property.2

def sectionHom (q : ℤ) : ((LocalCell).term ⟶ M q) →+
    (N (q-r)).val.obj (Opposite.op (Spec (CommRingCat.of New))) :=
  (ActualSheafContractionRestriction.pullback site (N (q-r)) (Projection).toRingHom).comp
    ((OriginalOrderedStrictSections.localEquiv J L G R κ n B hpos hneg hsupport hf hs site M N V r q i).toAddMonoidHom.comp
      (StrictCellTests.testAddEquiv J (LocalCell) (M q)).toAddMonoidHom)

def total (q : ℤ) : ((LocalCell).term ⟶ M q) →+ W.Total (CommRingCat.of New) :=
  (GradedSectionTotal.includeDegree (W.grading (CommRingCat.of New)) (q-r)).comp
    (sectionHom J L G R T κ n B hpos hneg hsupport hf hs r i site M N V q)

omit [HasFiniteBiproducts D] [L.Additive] [Nontrivial R] in
theorem total_apply (q : ℤ) (f : (LocalCell).term ⟶ M q) :
    total J L G R T κ n B hpos hneg hsupport hf hs r i site M N V W q f=
    GradedSectionTotal.includeDegree (W.grading (CommRingCat.of New)) (q-r)
      (OriginalFiberProjectionDetection.evaluation J L G R T κ n B hpos hneg hsupport hf hs r i site M N V q f) := rfl

#print axioms sectionHom
#print axioms total
#print axioms total_apply
end Verification.OriginalFiberTotalEvaluation
