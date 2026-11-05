/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalStrictAdjacentDifferential
import Verification.OriginalStrictContractionBlocks
import Verification.OriginalOrderedSectionDifferential

/-!
# Original Strict Contraction Differential

The whole actual strict sheaf differential is the sum of the actual
contraction-and-restriction blocks. Both the geometric boundary and every
source coordinate transport have been identified before this final sum.
-/
noncomputable section
namespace Verification.OriginalStrictContractionDifferential
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

include Q in
theorem block_contraction (p : ℕ) (b : ActualCellThom.Index κ n B (p+1)) (v : Selected n b.val) :
    OriginalStrictBoundaryConjugacy.block L G R κ n B hpos hneg hsupport hf hs E P p b
      (ActualGlobalBoundary.edgeIndex κ n B p b v) =
    (OriginalStrictContractionBlocks.contractionBlock L G E R κ n B P hpos hneg hsupport hf hs K U p b v)⟦(-1 : ℤ)⟧' ≫
      (shiftShiftNeg (L.obj (ActualCellThom.localThom G R κ n B p
        (ActualGlobalBoundary.edgeIndex κ n B p b v))) (1 : ℤ)).hom := by
  rw [OriginalStrictBoundaryGeometry.block_positive,
    OriginalStrictContractionBlocks.positive_eq_contraction L G E R κ n B P hpos hneg hsupport hf hs Q K U p b v]

include Q in
theorem section_contraction (p : ℕ) (j : ℤ)
    (a : (StrictCoefficientCochains.complex (Model).complex (M j)).X p)
    (b : ActualCellThom.Index κ n B (p+1)) :
    OriginalStrictSections.termEquiv J L G R T κ n B hpos hneg hsupport hf hs E P H empty site M N V (p+1) j
      ((StrictCoefficientCochains.complex (Model).complex (M j)).d p (p+1) a) b =
    OriginalStrictSections.localEquiv J L G R κ n B hpos hneg hsupport hf hs site M N V (p+1) j b
      ((StrictCoefficientBoundaryEvaluation.shiftTest J p (M j) _).symm
        (∑ v : b.val,
          (OriginalStrictContractionBlocks.contractionBlock L G E R κ n B P hpos hneg hsupport hf hs K U p b v)⟦(-1 : ℤ)⟧' ≫
          (shiftShiftNeg (L.obj (ActualCellThom.localThom G R κ n B p
            (ActualGlobalBoundary.edgeIndex κ n B p b v))) (1 : ℤ)).hom ≫
          (OriginalStrictSections.localEquiv J L G R κ n B hpos hneg hsupport hf hs site M N V p j
            (ActualGlobalBoundary.edgeIndex κ n B p b v)).symm
            (OriginalStrictSections.termEquiv J L G R T κ n B hpos hneg hsupport hf hs E P H empty site M N V p j a
              (ActualGlobalBoundary.edgeIndex κ n B p b v)))) := by
  rw [OriginalStrictAdjacentDifferential.section_adjacent]
  simp_rw [block_contraction L G R κ n B hpos hneg hsupport hf hs E P Q K U, Category.assoc]

include Q in
theorem ordered_section_contraction (p : ℕ) (j : ℤ)
    (a : (StrictCoefficientCochains.complex (Model).complex (M j)).X p)
    (b : ActualCellThom.Index κ n B (p+1)) :
    OriginalOrderedStrictSections.termEquiv J L G R T κ n B hpos hneg hsupport hf hs E P H empty site M N V (p+1) j
      ((StrictCoefficientCochains.complex (Model).complex (M j)).d p (p+1) a) b =
    OriginalOrderedStrictSections.localEquiv J L G R κ n B hpos hneg hsupport hf hs site M N V (p+1) j b
      ((StrictCoefficientBoundaryEvaluation.shiftTest J p (M j) _).symm
        (∑ v : b.val,
          (OriginalStrictContractionBlocks.contractionBlock L G E R κ n B P hpos hneg hsupport hf hs K U p b v)⟦(-1 : ℤ)⟧' ≫
          (shiftShiftNeg (L.obj (ActualCellThom.localThom G R κ n B p
            (ActualGlobalBoundary.edgeIndex κ n B p b v))) (1 : ℤ)).hom ≫
          (OriginalOrderedStrictSections.localEquiv J L G R κ n B hpos hneg hsupport hf hs site M N V p j
            (ActualGlobalBoundary.edgeIndex κ n B p b v)).symm
            (OriginalOrderedStrictSections.termEquiv J L G R T κ n B hpos hneg hsupport hf hs E P H empty site M N V p j a
              (ActualGlobalBoundary.edgeIndex κ n B p b v)))) := by
  rw [OriginalOrderedSectionDifferential.section_sum,
    OriginalStrictAdjacentDifferential.block_sum_adjacent]
  simp_rw [block_contraction L G R κ n B hpos hneg hsupport hf hs E P Q K U, Category.assoc]

#print axioms block_contraction
#print axioms section_contraction
#print axioms ordered_section_contraction
end Verification.OriginalStrictContractionDifferential
