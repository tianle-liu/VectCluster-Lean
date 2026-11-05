/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalStrictScalarEvaluation
import Verification.OriginalFiberProjectionDetection
import Verification.GradedMilnorWittScalarNaturality

/-!
# Original Fiber Scalar Evaluation

Ordinary scalar multiplication respects the actual canonical fiber projection.
-/
noncomputable section
set_option quotPrecheck false
namespace Verification.OriginalFiberScalarEvaluation
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
variable (P : GradedMilnorWittHomogeneity.Standard site N W)
variable (H : GradedMilnorWittStrictScalars.Standard J L G R site M N W P V)
local notation "Base" => GlobalNormalFrame.ZeroLayer R κ n i.val B
local notation "LocalCell" => StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs r i
local notation "Smooth" => IndependentCoordinatePurity.closed_smooth R κ n i.val B hpos hneg hsupport i.property.2
  (hf i.val i.property.2) (hs i.val i.property.2)

local notation "New" => ExchangeTransverseSlice.Fiber (ActualOpenChart.characters R (Selected n i.val)
  (Other n i.val ⊕ κ) (Other n i.val) (IndependentChartIndex.matrix κ n i.val B))
local notation "Projection" => OriginalCanonicalFiberProjection.projection R κ n i.val B hpos hneg hsupport i.property.2

include H in
omit [HasFiniteBiproducts D] [L.Additive] [Nontrivial R] in
theorem evaluate (k l : ℤ) (c : GradedMilnorWittDegreeSpaces.space site N W (CommRingCat.of R) (l-k))
    (f : (LocalCell).term ⟶ M k) :
    GradedSectionTotal.includeDegree (W.grading (CommRingCat.of New)) (l-r)
      (OriginalFiberProjectionDetection.evaluation J L G R T κ n B hpos hneg hsupport hf hs r i site M N V l
        (f ≫ H.scalar k l c)) =
    GradedSectionTotal.includeDegree (W.grading (CommRingCat.of New)) (k-r)
      (OriginalFiberProjectionDetection.evaluation J L G R T κ n B hpos hneg hsupport hf hs r i site M N V k f)*
      GradedMilnorWittScalarNaturality.scalar R New site N W c.val := by
  have h := congrArg (GradedMilnorWittSheaf.pullback site N W
    (S:=CommRingCat.of Base) (T:=CommRingCat.of New) (Projection).toRingHom)
    (OriginalStrictScalarEvaluation.evaluate J L G R T κ n B hpos hneg hsupport hf hs r i
      site M N V W P H k l c f)
  rw [map_mul] at h
  simp only [GradedMilnorWittSheaf.pullback_degree] at h
  change _ = _ * GradedMilnorWittSheaf.pullback site N W
    (S:=CommRingCat.of Base) (T:=CommRingCat.of New) (Projection).toRingHom
      (GradedMilnorWittScalarNaturality.scalar R Base site N W c.val) at h
  rw [GradedMilnorWittScalarNaturality.naturality R Base New site N W Projection] at h
  rw [GradedMilnorWittSheaf.pullback_degree (S:=CommRingCat.of Base) (T:=CommRingCat.of New)
    site N W (Projection).toRingHom (l-r),
    GradedMilnorWittSheaf.pullback_degree (S:=CommRingCat.of Base) (T:=CommRingCat.of New)
    site N W (Projection).toRingHom (k-r)] at h
  exact h

#print axioms evaluate
end Verification.OriginalFiberScalarEvaluation
