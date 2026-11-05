/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalKZeroBundleRange
import Verification.SevenfoldActualIndependentSets

/-!
# Sevenfold Bundle Range

Freeness and single-line stabilization for actual bundles on the sevenfold.
-/
noncomputable section
namespace Verification.SevenfoldBundleRange
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open Verification.StrictProjectiveModel Verification.FrozenAcyclicCover
open Verification.ExchangeOpenCover
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasBinaryBiproducts A]
variable [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
variable [∀ z : ℤ, (shiftFunctor D z).Additive] [Pretriangulated D] [HasFiniteBiproducts D]
variable (J : DerivedCategory A ⥤ D) [J.Additive] [J.CommShift ℤ] [J.IsTriangulated]
variable (L : DerivedCategory C ⥤ D) [L.Additive] [L.CommShift ℤ] [L.IsTriangulated]
variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (R : Type) [Field R]
variable (T : StrictLocalizedCells.TorusCells J L G R)
variable (E : OpenConeExcision.StandardExcision G) (P : LocalizedCoordinatePurity.Standard L R G)
variable (H : ChainRepresentability (A := A))
variable (empty : ∀ X : Scheme,IsEmpty X → IsZero (L.obj (DerivedCategory.Q.obj (G.obj X))))


open Verification.OriginalBundleRange

variable (HC : StrictCoefficientComparison.StandardHomology (A := A))
variable (Det : DeterminantStandardInput.Standard (Global R (Fin 2) 5 SevenfoldExchangeMatrix.matrix))
variable (N : letI := originalDomain R (Fin 2) 5 SevenfoldExchangeMatrix.matrix SevenfoldExchangeMatrix.positive_order SevenfoldExchangeMatrix.negative_order SevenfoldExchangeMatrix.support (fun I hI => (SevenfoldExchangeMatrix.selected_AS I hI).1) (fun I hI => (SevenfoldExchangeMatrix.selected_AS I hI).2); OrientedLineStabilization.Naturality Det)
variable (F : Type) [Field F] [Algebra (Global R (Fin 2) 5 SevenfoldExchangeMatrix.matrix) F]
variable {KG : Scheme → Type*} [∀ X,AddCommGroup (KG X)]
variable (GT : SchemeGZeroInput.Theory KG) (GK : SchemeGZeroInput.Koszul GT)
variable (GTorus : SchemeGZeroInput.SplitAffineTorus GT) (GLocalization : SchemeGZeroInput.Localization GT)
variable (SC : SmoothCartanInput.Standard)
variable (S : letI := originalDomain R (Fin 2) 5 SevenfoldExchangeMatrix.matrix SevenfoldExchangeMatrix.positive_order SevenfoldExchangeMatrix.negative_order SevenfoldExchangeMatrix.support (fun I hI => (SevenfoldExchangeMatrix.selected_AS I hI).1) (fun I hI => (SevenfoldExchangeMatrix.selected_AS I hI).2); ∀ r,2≤r → AmbientPostnikovStages.StabilizationStages Det N J
  (L.obj (DerivedCategory.Q.obj (G.obj (Spec (CommRingCat.of (Global R (Fin 2) 5 SevenfoldExchangeMatrix.matrix)))))) r)

include T E P H empty HC F GT GK GTorus GLocalization SC S in
theorem free_above (Q : ActualProjectiveSplitting.Bundle (SevenfoldExchangeMatrix.Ring R)) {r : ℕ}
    (hr : ActualProjectiveSplitting.HasRank Q r) (hh : 2<r) : ActualProjectiveSplitting.Trivial Q := by
  apply OriginalKZeroBundleRange.free_above J L G R T (Fin 2) 5 SevenfoldExchangeMatrix.matrix SevenfoldExchangeMatrix.positive_order SevenfoldExchangeMatrix.negative_order SevenfoldExchangeMatrix.support (fun I hI => (SevenfoldExchangeMatrix.selected_AS I hI).1) (fun I hI => (SevenfoldExchangeMatrix.selected_AS I hI).2) E P H empty HC Det N F GT GK GTorus GLocalization SC S Q hr
  change PrimeIndependentHeight.height (Fin 5)
    (Independent (laterWeights (Fin 2) 5 SevenfoldExchangeMatrix.matrix)) < r
  rwa [SevenfoldActualIndependentSets.height_eq_two]

include T E P H empty HC F GT GK GTorus GLocalization SC S in
theorem one_line_stable (Q : ActualProjectiveSplitting.Bundle (SevenfoldExchangeMatrix.Ring R))
    (hr : ActualProjectiveSplitting.HasRank Q 2) :
    Nonempty ((Q.object × SevenfoldExchangeMatrix.Ring R) ≃ₗ[SevenfoldExchangeMatrix.Ring R]
      (Fin 3 → SevenfoldExchangeMatrix.Ring R)) := by
  apply OriginalKZeroBundleRange.one_line_stable J L G R T (Fin 2) 5 SevenfoldExchangeMatrix.matrix SevenfoldExchangeMatrix.positive_order SevenfoldExchangeMatrix.negative_order SevenfoldExchangeMatrix.support (fun I hI => (SevenfoldExchangeMatrix.selected_AS I hI).1) (fun I hI => (SevenfoldExchangeMatrix.selected_AS I hI).2) E P H empty HC Det N F GT GK GTorus GLocalization SC S _ Q hr
  change PrimeIndependentHeight.height (Fin 5)
    (Independent (laterWeights (Fin 2) 5 SevenfoldExchangeMatrix.matrix)) ≤ 2
  rw [SevenfoldActualIndependentSets.height_eq_two]

include T E P H empty HC F GT GK GTorus GLocalization SC S in
theorem free_other (Q : ActualProjectiveSplitting.Bundle (SevenfoldExchangeMatrix.Ring R)) {r : ℕ}
    (hr : ActualProjectiveSplitting.HasRank Q r) (hpos : 0<r) (hne : r≠2) :
    ActualProjectiveSplitting.Trivial Q := by
  by_cases h1 : r=1
  · subst r
    letI := SevenfoldExchangeMatrix.domain R
    exact StableOrientations.line_free_of_kzero Det F
      (OriginalKZero.rank_bijective R (Fin 2) 5 SevenfoldExchangeMatrix.matrix SevenfoldExchangeMatrix.positive_order SevenfoldExchangeMatrix.negative_order SevenfoldExchangeMatrix.support (fun I hI => (SevenfoldExchangeMatrix.selected_AS I hI).1) (fun I hI => (SevenfoldExchangeMatrix.selected_AS I hI).2) GT GK GTorus GLocalization SC F).1 Q hr
  · exact free_above J L G R T E P H empty HC Det N F GT GK GTorus GLocalization SC S Q hr (by omega)

#print axioms free_above
#print axioms one_line_stable
#print axioms free_other
end Verification.SevenfoldBundleRange
