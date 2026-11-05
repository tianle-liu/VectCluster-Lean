/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalStrictLocalBlocks
import Verification.OriginalStrictBoundaryGeometry

/-!
# Original Strict Nonincident Block

Nonincident literal strict-model blocks vanish by genuine geometric boundary vanishing and the actual universal test equivalence.
-/
noncomputable section
set_option quotPrecheck false
namespace Verification.OriginalStrictNonincidentBlock
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

attribute [local instance] Abelian.hasFiniteBiproducts

local notation "Model" => OriginalPositiveCellular.model J L G R T κ n B hpos hneg hsupport hf hs E P H empty

open scoped BigOperators

theorem zero (p : ℕ) (b : ActualCellThom.Index κ n B (p+1)) (i : ActualCellThom.Index κ n B p)
    (h : ¬ i.val ⊆ b.val) :
    OriginalStrictLocalBlocks.block J L G R T κ n B hpos hneg hsupport hf hs E P H empty p b i=0 := by
  let F := (StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs p i).term
  let a := OriginalStrictLocalBlocks.coefficient J L G R T κ n B hpos hneg hsupport hf hs E P H empty F p i (𝟙 F)
  have hh := OriginalStrictBoundaryConjugacy.coefficient_sum J L G R T κ n B hpos hneg hsupport hf hs
    E P H empty p F a b
  dsimp only [a] at hh
  rw [OriginalStrictLocalBlocks.differential_test,Category.comp_id] at hh
  have hz : ∑ k : ActualCellThom.Index κ n B p,
      OriginalStrictBoundaryConjugacy.block L G R κ n B hpos hneg hsupport hf hs E P p b k ≫
        OriginalStrictCellTests.termEquiv J L G R T κ n B hpos hneg hsupport hf hs E P H empty F p a k=0 := by
    apply Finset.sum_eq_zero
    intro k _
    by_cases he : k=i
    · subst k
      rw [OriginalStrictBoundaryGeometry.nonincident L G E R κ n B P hpos hneg hsupport hf hs p b i h,zero_comp]
    · dsimp only [a]
      rw [OriginalStrictLocalBlocks.coefficient_other J L G R T κ n B hpos hneg hsupport hf hs E P H empty F p i k he,comp_zero]
  apply (StrictCellTests.testAddEquiv J
    (StrictLocalizedCells.localCell J L G R T κ n B hpos hneg hsupport hf hs (p+1) b) F).injective
  rw [hh,map_zero]
  change (StrictCoefficientBoundaryEvaluation.shiftTest J p F _).symm _=0
  rw [hz,map_zero]

#print axioms zero
end Verification.OriginalStrictNonincidentBlock
