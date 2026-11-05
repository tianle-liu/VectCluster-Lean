/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalStrictProjectionDetection
import Verification.OriginalFiberSectionIso

/-!
# Original Fiber Projection Detection

Genuine original local arrows are detected after the already constructed canonical fiber projection.
-/
noncomputable section
set_option quotPrecheck false
namespace Verification.OriginalFiberProjectionDetection
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

attribute [local instance] Abelian.hasFiniteBiproducts
variable (r s : ℕ) (a : ActualCellThom.Index κ n B r) (b : ActualCellThom.Index κ n B s)
variable (τ α σ β : Type) [Fintype τ] [Fintype α] [LinearOrder α] [Fintype σ] [Fintype β] [LinearOrder β]
variable (ea : GlobalNormalFrame.ZeroLayer R κ n a.val B ≃ₐ[R] TorusThomInput.BaseRing R τ α)
variable (eb : GlobalNormalFrame.ZeroLayer R κ n b.val B ≃ₐ[R] TorusThomInput.BaseRing R σ β)
variable (site : GrothendieckTopology Scheme.{0}) (M : ℤ → A)
variable (N : ℤ → Sheaf site (ModuleCat.{0} ℤ)) (V : LocalizedThomSections.Standard J L G R site M N)
variable (Z₀ : A) (W : GradedMilnorWittSheaf.Standard site N)
variable (Q : StrictTorusSymbolInput.Standard J L G R T Z₀ M site N W V)
local notation "SourceCell" => StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs r a
local notation "TargetCell" => StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs s b

variable [HasShift D ℤ] [∀ q : ℤ, (shiftFunctor D q).Additive] [HasZeroObject D] [Pretriangulated D]
variable [J.CommShift ℤ] [L.CommShift ℤ] [L.IsTriangulated]
variable (U : LocalizedAffineThomInvariance.Standard L R G)
variable (hV : LocalizedThomSections.Naturality J L G R site M N V)
variable (v : Selected n a.val)
local notation "New" => ExchangeTransverseSlice.Fiber (ActualOpenChart.characters R (Selected n a.val)
  (Other n a.val ⊕ κ) (Other n a.val) (IndependentChartIndex.matrix κ n a.val B))

def evaluation (q : ℤ) (f : (SourceCell).term ⟶ M q) :
    (N (q-r)).val.obj (Opposite.op (Spec (CommRingCat.of New))) :=
  ActualSheafContractionRestriction.pullback site (N (q-r))
    (OriginalCanonicalFiberProjection.projection R κ n a.val B hpos hneg hsupport a.property.2).toRingHom
    (OriginalOrderedStrictSections.localEquiv J L G R κ n B hpos hneg hsupport hf hs site M N V r q a
      (StrictCellTests.testAddEquiv J (SourceCell) (M q) f))

include ea U hV v in
omit [HasFiniteBiproducts D] [L.Additive] [Nontrivial R] [∀ q : ℤ, (shiftFunctor D q).Additive]
  [HasZeroObject D] [Pretriangulated D] [J.CommShift ℤ] [L.CommShift ℤ] [L.IsTriangulated] [HasShift D ℤ] in
theorem detect (hr : 0<r) (d m : (SourceCell).term ⟶ (TargetCell).term)
    (h : ∀ (i : BinaryWordCoordinates.Index (Fintype.card β))
      (hi : StrictTorusSymbolInput.degree (Fintype.card (Fin s)) (Fintype.card β) i≠0),
      GradedSectionTotal.includeDegree (W.grading (CommRingCat.of New))
        (StrictTorusSymbolInput.degree (Fintype.card (Fin s)) (Fintype.card β) i-r)
        (evaluation J L G R T κ n B hpos hneg hsupport hf hs r a site M N V _
          (d ≫ OriginalCoordinateProjectionSymbols.projection J L G R T κ n B hpos hneg hsupport hf hs
            s b σ β eb site M N V Z₀ W Q i hi)) =
      GradedSectionTotal.includeDegree (W.grading (CommRingCat.of New))
        (StrictTorusSymbolInput.degree (Fintype.card (Fin s)) (Fintype.card β) i-r)
        (evaluation J L G R T κ n B hpos hneg hsupport hf hs r a site M N V _
          (m ≫ OriginalCoordinateProjectionSymbols.projection J L G R T κ n B hpos hneg hsupport hf hs
            s b σ β eb site M N V Z₀ W Q i hi))) : d=m := by
  apply OriginalStrictProjectionDetection.detect J L G R T κ n B hpos hneg hsupport hf hs
    r s a b τ α σ β ea eb site M N V Z₀ W Q hr d m
  intro i hi
  apply congrArg (GradedSectionTotal.includeDegree
    (W.grading (CommRingCat.of (GlobalNormalFrame.ZeroLayer R κ n a.val B))) _)
  apply (OriginalFiberSectionIso.sections J L G R κ n a.val B v U hpos hneg hsupport a.property.2
    (hf a.val a.property.2) (hs a.val a.property.2) r
    ((Fintype.card_coe a.val).trans a.property.1) site M N V _).injective
  simp_rw [OriginalFiberSectionIso.sections_apply J L G R κ n a.val B v U hpos hneg hsupport a.property.2
    (hf a.val a.property.2) (hs a.val a.property.2) r
    ((Fintype.card_coe a.val).trans a.property.1) site M N V hV]
  exact GradedSectionTotal.includeDegree_injective (W.grading (CommRingCat.of New)) _ (h i hi)

#print axioms evaluation
#print axioms detect
end Verification.OriginalFiberProjectionDetection
