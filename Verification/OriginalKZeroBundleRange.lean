/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalKZero
import Verification.OriginalBundleRange
import Verification.OriginalStrictCohomology
import Verification.OriginalScalarOne
import Verification.StrictModelBundleRange
import Verification.StrictModelEulerClassification

/-!
# Original K Zero Bundle Range

The actual exchange-ring bundle range with its K_0 hypothesis
now discharged by the constructed global G-theory filtration. The model,
integrality, cohomological bound and rank comparison are derived; only
uniform ordinary reference theories remain as inputs.
-/
noncomputable section
namespace Verification.OriginalKZeroBundleRange
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open Verification.StrictProjectiveModel Verification.FrozenAcyclicCover
open Verification.ExchangeOpenCover
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasBinaryBiproducts A]
variable [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
variable [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [HasFiniteBiproducts D]
variable (J : DerivedCategory A ⥤ D) [J.Additive] [J.CommShift ℤ] [J.IsTriangulated]
variable (L : DerivedCategory C ⥤ D) [L.Additive] [L.CommShift ℤ] [L.IsTriangulated]
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (R : Type) [Field R]
variable (T : StrictLocalizedCells.TorusCells J L G R)
variable (κ : Type) [Fintype κ] (n : ℕ) (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j,earlierWeights κ n B i j=0 ↔ laterWeights κ n B i j=0)
variable (hf : ∀ I,Independent (laterWeights κ n B) I → Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (hs : ∀ I,Independent (laterWeights κ n B) I → FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)))
variable (E : OpenConeExcision.StandardExcision G) (P : LocalizedCoordinatePurity.Standard L R G)
variable (H : ChainRepresentability (A := A))
variable (empty : ∀ X : Scheme,IsEmpty X → IsZero (L.obj (DerivedCategory.Q.obj (G.obj X))))


open Verification.OriginalBundleRange

variable (HC : StrictCoefficientComparison.StandardHomology (A := A))
variable (Det : DeterminantStandardInput.Standard (Global R κ n B))
variable (N : letI := originalDomain R κ n B hpos hneg hsupport hf hs; OrientedLineStabilization.Naturality Det)
variable (F : Type) [Field F] [Algebra (Global R κ n B) F]
variable {KG : Scheme → Type*} [∀ X,AddCommGroup (KG X)]
variable (GT : SchemeGZeroInput.Theory KG) (GK : SchemeGZeroInput.Koszul GT)
variable (GTorus : SchemeGZeroInput.SplitAffineTorus GT) (GLocalization : SchemeGZeroInput.Localization GT)
variable (SC : SmoothCartanInput.Standard)
variable (S : letI := originalDomain R κ n B hpos hneg hsupport hf hs; ∀ r,2≤r → AmbientPostnikovStages.StabilizationStages Det N J
  (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of (Global R κ n B)))))) r)

include T hpos hneg hsupport hf hs E P H empty HC F GT GK GTorus GLocalization SC S in
theorem free_above (Q : ActualProjectiveSplitting.Bundle (Global R κ n B)) {r : ℕ}
    (hr : ActualProjectiveSplitting.HasRank Q r) (hh : StrictCellularGlobal.height κ n B<r) :
    ActualProjectiveSplitting.Trivial Q := by
  have hk := (OriginalKZero.rank_bijective R κ n B hpos hneg hsupport hf hs GT GK GTorus GLocalization SC F).1
  letI := originalDomain R κ n B hpos hneg hsupport hf hs
  exact StrictModelBundleRange.free_above Det N F HC
    (StrictCellularGlobal.globalModel J L G R T κ n B hpos hneg hsupport hf hs E P H empty)
    (StrictCellularGlobal.support_upper J L G R T κ n B hpos hneg hsupport hf hs E P H empty)
    (StrictCellularGlobal.support_lower J L G R T κ n B hpos hneg hsupport hf hs E P H empty)
    S hk Q hr hh

include T hpos hneg hsupport hf hs E P H empty HC F GT GK GTorus GLocalization SC S in
theorem one_line_stable (hh : StrictCellularGlobal.height κ n B≤2)
    (Q : ActualProjectiveSplitting.Bundle (Global R κ n B)) (hr : ActualProjectiveSplitting.HasRank Q 2) :
    Nonempty ((Q.object × Global R κ n B) ≃ₗ[Global R κ n B] (Fin 3 → Global R κ n B)) := by
  have hk := (OriginalKZero.rank_bijective R κ n B hpos hneg hsupport hf hs GT GK GTorus GLocalization SC F).1
  letI := originalDomain R κ n B hpos hneg hsupport hf hs
  exact StrictModelBundleRange.one_line_stable Det N F HC
    (StrictCellularGlobal.globalModel J L G R T κ n B hpos hneg hsupport hf hs E P H empty)
    (StrictCellularGlobal.support_upper J L G R T κ n B hpos hneg hsupport hf hs E P H empty)
    (StrictCellularGlobal.support_lower J L G R T κ n B hpos hneg hsupport hf hs E P H empty)
    S hk hh Q hr

include T hpos hneg hsupport hf hs E P H empty HC F GT GK GTorus GLocalization SC S in
theorem all_free (hh : StrictCellularGlobal.height κ n B≤1)
    (Q : ActualProjectiveSplitting.Bundle (Global R κ n B)) : ActualProjectiveSplitting.Trivial Q := by
  have hk := (OriginalKZero.rank_bijective R κ n B hpos hneg hsupport hf hs GT GK GTorus GLocalization SC F).1
  letI := originalDomain R κ n B hpos hneg hsupport hf hs
  exact StrictModelBundleRange.all_free Det N F HC
    (StrictCellularGlobal.globalModel J L G R T κ n B hpos hneg hsupport hf hs E P H empty)
    (StrictCellularGlobal.support_upper J L G R T κ n B hpos hneg hsupport hf hs E P H empty)
    (StrictCellularGlobal.support_lower J L G R T κ n B hpos hneg hsupport hf hs E P H empty)
    S hk hh Q

#print axioms free_above
#print axioms one_line_stable
#print axioms all_free
end Verification.OriginalKZeroBundleRange
