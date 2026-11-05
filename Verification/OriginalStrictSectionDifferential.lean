/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalStrictSections
import Verification.OriginalStrictBoundaryConjugacy

/-!
# Original Strict Section Differential

The original sheaf-section differential is the whole actual ambient
Thom boundary matrix under the already constructed section equivalences.
-/
noncomputable section
namespace Verification.OriginalStrictSectionDifferential
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

theorem section_sum (p : ℕ) (j : ℤ)
    (a : (StrictCoefficientCochains.complex (Model).complex (M j)).X p)
    (b : ActualCellThom.Index κ n B (p+1)) :
    OriginalStrictSections.termEquiv J L G R T κ n B hpos hneg hsupport hf hs E P H empty site M N V (p+1) j
      ((StrictCoefficientCochains.complex (Model).complex (M j)).d p (p+1) a) b =
    OriginalStrictSections.localEquiv J L G R κ n B hpos hneg hsupport hf hs site M N V (p+1) j b
      ((StrictCoefficientBoundaryEvaluation.shiftTest J p (M j) _).symm
        (∑ i : ActualCellThom.Index κ n B p,
          OriginalStrictBoundaryConjugacy.block L G R κ n B hpos hneg hsupport hf hs E P p b i ≫
            (OriginalStrictSections.localEquiv J L G R κ n B hpos hneg hsupport hf hs site M N V p j i).symm
              (OriginalStrictSections.termEquiv J L G R T κ n B hpos hneg hsupport hf hs E P H empty site M N V p j a i))) := by
  simp only [OriginalStrictSections.termEquiv,AddEquiv.trans_apply,
    AddEquiv.piCongrRight_apply,AddEquiv.symm_apply_apply]
  rw [OriginalStrictBoundaryConjugacy.coefficient_sum]

#print axioms section_sum
end Verification.OriginalStrictSectionDifferential
