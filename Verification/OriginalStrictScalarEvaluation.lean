/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GradedStrictScalarEvaluation
import Verification.OriginalOrderedStrictSections

/-!
# Original Strict Scalar Evaluation

The actual original strict-cell tests respect ordinary homogeneous
MW scalar morphisms, including the canonical increasing normal numbering.
-/
noncomputable section
set_option quotPrecheck false
namespace Verification.OriginalStrictScalarEvaluation
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

include H in
omit [HasFiniteBiproducts D] [L.Additive] [Nontrivial R] in
theorem evaluate (k l : ℤ) (c : GradedMilnorWittDegreeSpaces.space site N W (CommRingCat.of R) (l-k))
    (f : (LocalCell).term ⟶ M k) :
    GradedSectionTotal.includeDegree (W.grading (CommRingCat.of Base)) (l-r)
      (OriginalOrderedStrictSections.localEquiv J L G R κ n B hpos hneg hsupport hf hs site M N V r l i
        (StrictCellTests.testAddEquiv J (LocalCell) (M l) (f ≫ H.scalar k l c)))=
    GradedSectionTotal.includeDegree (W.grading (CommRingCat.of Base)) (k-r)
      (OriginalOrderedStrictSections.localEquiv J L G R κ n B hpos hneg hsupport hf hs site M N V r k i
        (StrictCellTests.testAddEquiv J (LocalCell) (M k) f))*
      GradedMilnorWittSheaf.pullback site N W (S := CommRingCat.of R) (T := CommRingCat.of Base)
        (algebraMap R Base) c.val := by
  rw [StrictCellTests.test_natural]
  exact GradedStrictScalarEvaluation.ordered J L G R site M N W P V H Base (Selected n i.val) r
    ((Fintype.card_coe i.val).trans i.property.1) Smooth k l c _

#print axioms evaluate
end Verification.OriginalStrictScalarEvaluation
