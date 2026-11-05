/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OrderedExplicitCoordinateEvaluation
import Verification.StrictTorusSymbolRedegree
import Verification.OriginalOrderedStrictSections

/-!
# Original Coordinate Projection Symbols

Actual local strict-cell projections in any explicitly constructed
coordinate chart have the ordinary universal torus symbols. The comparison
is proved from the genuine Thom coordinate map and its evaluation square.
-/
noncomputable section
set_option quotPrecheck false
namespace Verification.OriginalCoordinateProjectionSymbols
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
variable (τ α : Type) [Fintype τ] [Fintype α]
variable (e : GlobalNormalFrame.ZeroLayer R κ n i.val B ≃ₐ[R] TorusThomInput.BaseRing R τ α)

variable (site : GrothendieckTopology Scheme.{0}) (M : ℤ → A)
variable (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (V : LocalizedThomSections.Standard J L G R site M N)
variable (hV : LocalizedThomSections.Naturality J L G R site M N V)
local notation "Base" => GlobalNormalFrame.ZeroLayer R κ n i.val B
local notation "Std" => TorusThomInput.BaseRing R τ α
local notation "LocalCell" => StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs r i
local notation "StdCell" => StrictLocalizedCoordinateTransport.standardCell J L G R T r τ α
local notation "Coord" => StrictLocalizedCoordinateTransport.termIso J L G R T κ n B hpos hneg hsupport hf hs r i τ α e
local notation "Smooth" => IndependentCoordinatePurity.closed_smooth R κ n i.val B hpos hneg hsupport i.property.2
  (hf i.val i.property.2) (hs i.val i.property.2)

include hV in
omit [HasFiniteBiproducts D] [L.Additive] [Nontrivial R] in
theorem evaluation (q : ℤ) (a : (StdCell).term ⟶ M q) :
    (N (q-r)).val.map (Spec.map (CommRingCat.ofHom e.toRingEquiv.toRingHom)).op
      (OriginalOrderedStrictSections.localEquiv J L G R κ n B hpos hneg hsupport hf hs site M N V r q i
        (StrictCellTests.testAddEquiv J (LocalCell) (M q) ((Coord).hom ≫ a)))=
    OrderedThomEvaluation.finEvaluate J L G R site M N V Std r
      (StrictTorusSymbolInput.baseSmooth R τ α) q
      (StrictCellTests.testAddEquiv J (StdCell) (M q) a) := by
  rw [StrictLocalizedCoordinateTransport.test]
  change (N (q-r)).val.map (Spec.map (CommRingCat.ofHom e.toRingEquiv.toRingHom)).op
    (OrderedThomSections.evaluate (Selected n i.val) r ((Fintype.card_coe i.val).trans i.property.1)
      Base J L G R site M N V Smooth q
      (L.map ((OrderedThomBaseChange.baseIso e.toRingEquiv G (Selected n i.val)).hom ≫
        (OrderedThomSections.thomIso (Selected n i.val) r
          ((Fintype.card_coe i.val).trans i.property.1) Std G).hom) ≫
        StrictCellTests.testAddEquiv J (StdCell) (M q) a))=_
  exact OrderedExplicitCoordinateEvaluation.evaluate (Selected n i.val) r
    ((Fintype.card_coe i.val).trans i.property.1) J L G R site M N V hV e Smooth
      (StrictTorusSymbolInput.baseSmooth R τ α) q _

variable (Z : A) [LinearOrder α]
variable (W : GradedMilnorWittSheaf.Standard site N)
variable (Q : StrictTorusSymbolInput.Standard J L G R T Z M site N W V)

def projection (w : BinaryWordCoordinates.Index (Fintype.card α))
    (hw : StrictTorusSymbolInput.degree (Fintype.card (Fin r)) (Fintype.card α) w≠0) :
    (LocalCell).term ⟶ M (StrictTorusSymbolInput.degree (Fintype.card (Fin r)) (Fintype.card α) w) :=
  (Coord).hom ≫ StrictTorusSymbolRedegree.projection J L G R T Z M site N W V Q
    (Fin r) τ α r (Fintype.card_fin r) w hw

include hV in
omit [HasFiniteBiproducts D] [L.Additive] [Nontrivial R] in
theorem symbols (w : BinaryWordCoordinates.Index (Fintype.card α))
    (hw : StrictTorusSymbolInput.degree (Fintype.card (Fin r)) (Fintype.card α) w≠0) :
    GradedSectionTotal.includeDegree (W.grading (CommRingCat.of Std))
      (StrictTorusSymbolInput.degree (Fintype.card (Fin r)) (Fintype.card α) w-r)
      ((N (StrictTorusSymbolInput.degree (Fintype.card (Fin r)) (Fintype.card α) w-r)).val.map
        (Spec.map (CommRingCat.ofHom e.toRingEquiv.toRingHom)).op
        (OriginalOrderedStrictSections.localEquiv J L G R κ n B hpos hneg hsupport hf hs site M N V r _ i
          (StrictCellTests.testAddEquiv J (LocalCell) _
            (projection J L G R T κ n B hpos hneg hsupport hf hs r i τ α e site M N V Z W Q w hw))))=
    OrderedBinaryWords.word (Fintype.card α)
      (fun k => (W.symbols (CommRingCat.of Std)).symbol (StrictTorusSymbolInput.baseUnit R τ α k)) w := by
  unfold projection
  rw [evaluation J L G R T κ n B hpos hneg hsupport hf hs r i τ α e site M N V hV]
  simp only [OrderedThomEvaluation.finEvaluate,OrderedThomEvaluation.rewrite_eq_degree]
  exact StrictTorusSymbolRedegree.symbols J L G R T Z M site N W V Q
    (Fin r) τ α r (Fintype.card_fin r) w hw

#print axioms evaluation
#print axioms projection
#print axioms symbols
end Verification.OriginalCoordinateProjectionSymbols
