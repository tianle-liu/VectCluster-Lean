/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalCoordinateProjectionSymbols
import Verification.StrictTorusSymbolDetection

/-!
# Original Strict Projection Detection

Positive universal projection tests determine genuine original local-cell arrows; the integer component is treated using its ordinary vanishing contraction.
-/
noncomputable section
set_option quotPrecheck false
namespace Verification.OriginalStrictProjectionDetection
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

def splitSource : (SourceCell).term ≅ ⨁ (StrictTorusSymbolInput.summand Z₀ M (Fintype.card (Fin r)) (Fintype.card α)) :=
  StrictLocalizedCoordinateTransport.termIso J L G R T κ n B hpos hneg hsupport hf hs r a τ α ea ≪≫
    StrictTorusSymbolRedegree.split J L G R T Z₀ M site N W V Q (Fin r) τ α r (Fintype.card_fin r)

include ea in
omit [L.Additive] [Nontrivial R] [HasFiniteBiproducts D] in
theorem detect (hr : 0<r) (d m : (SourceCell).term ⟶ (TargetCell).term)
    (h : ∀ (i : BinaryWordCoordinates.Index (Fintype.card β))
      (hi : StrictTorusSymbolInput.degree (Fintype.card (Fin s)) (Fintype.card β) i≠0),
      GradedSectionTotal.includeDegree (W.grading (CommRingCat.of (GlobalNormalFrame.ZeroLayer R κ n a.val B)))
        (StrictTorusSymbolInput.degree (Fintype.card (Fin s)) (Fintype.card β) i-r)
        (OriginalOrderedStrictSections.localEquiv J L G R κ n B hpos hneg hsupport hf hs site M N V r _ a
          (StrictCellTests.testAddEquiv J (SourceCell) _
            (d ≫ OriginalCoordinateProjectionSymbols.projection J L G R T κ n B hpos hneg hsupport hf hs
              s b σ β eb site M N V Z₀ W Q i hi))) =
      GradedSectionTotal.includeDegree (W.grading (CommRingCat.of (GlobalNormalFrame.ZeroLayer R κ n a.val B)))
        (StrictTorusSymbolInput.degree (Fintype.card (Fin s)) (Fintype.card β) i-r)
        (OriginalOrderedStrictSections.localEquiv J L G R κ n B hpos hneg hsupport hf hs site M N V r _ a
          (StrictCellTests.testAddEquiv J (SourceCell) _
            (m ≫ OriginalCoordinateProjectionSymbols.projection J L G R T κ n B hpos hneg hsupport hf hs
              s b σ β eb site M N V Z₀ W Q i hi)))) : d=m := by
  let et := splitSource J L G R T κ n B hpos hneg hsupport hf hs s b σ β eb site M N V Z₀ W Q
  apply (cancel_mono et.hom).1
  apply biproduct.hom_ext
  intro i
  by_cases hi : StrictTorusSymbolInput.degree (Fintype.card (Fin s)) (Fintype.card β) i=0
  · have he : StrictTorusSymbolInput.summand Z₀ M (Fintype.card (Fin s)) (Fintype.card β) i=Z₀ := if_pos hi
    apply (cancel_mono (eqToHom he)).1
    have hp : 0<Fintype.card (Fin r) := by simpa only [Fintype.card_fin] using hr
    exact (StrictTorusSymbolDetection.integer_zero Z₀ M Q.integer_contraction _ _ hp
      (splitSource J L G R T κ n B hpos hneg hsupport hf hs r a τ α ea site M N V Z₀ W Q) _).trans
      (StrictTorusSymbolDetection.integer_zero Z₀ M Q.integer_contraction _ _ hp
        (splitSource J L G R T κ n B hpos hneg hsupport hf hs r a τ α ea site M N V Z₀ W Q) _).symm
  · have hsec := GradedSectionTotal.includeDegree_injective
      (W.grading (CommRingCat.of (GlobalNormalFrame.ZeroLayer R κ n a.val B))) _ (h i hi)
    have ht := (OriginalOrderedStrictSections.localEquiv J L G R κ n B hpos hneg hsupport hf hs
      site M N V r _ a).injective hsec
    have hh := (StrictCellTests.testAddEquiv J (SourceCell) _).injective ht
    apply (cancel_mono (eqToHom (if_neg hi))).1
    simpa only [et,splitSource,Iso.trans_hom,OriginalCoordinateProjectionSymbols.projection,
      StrictTorusSymbolRedegree.split,StrictTorusSymbolRedegree.projection,
      StrictTorusSymbolInput.positiveProjection,StrictTorusSymbolInput.projection,Category.assoc] using hh

#print axioms splitSource
#print axioms detect
end Verification.OriginalStrictProjectionDetection
