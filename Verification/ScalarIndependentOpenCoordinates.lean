/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarGlobalSmooth

/-!
# Scalar Independent Open Coordinates

The equivalence from a principal open of the fixed global exchange
presentation to its selected chart preserves the original x coordinates.
-/
noncomputable section
namespace Verification.ScalarIndependentOpenCoordinates
open Verification.ScalarFrozenGlobal Verification.IndependentChartIndex
open Verification.ScalarIndependentBasicOpen
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ) (I : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (a b : Fin n → Rˣ)
attribute [local instance] MvPolynomial.algebraMvPolynomial

def selectedCoordinate (i : Selected n I) : BasicOpen R κ n I B a b :=
  algebraMap (Global R κ n B a b) (BasicOpen R κ n I B a b) (initial R κ n B a b (Sum.inl i.1))

theorem presentation_openEquiv_original (q : Fin n ⊕ κ) :
    ScalarIndependentChartPresentation.openEquiv R κ n I B a b
      (algebraMap (Presentation R κ n B a b)
        (Localization (ScalarIndependentChartPresentation.complementMonoid R κ n I B a b))
        (original R κ n B a b q)) =
      algebraMap (ScalarIndependentChartPresentation.NewPresentation R κ n I B a b)
        (ScalarActualOpenChart.GlobalOpen R (Selected n I) (Other n I ⊕ κ) (Other n I)
          (ScalarIndependentChartPresentation.newScalar R n I a)
          (ScalarIndependentChartPresentation.newScalar R n I b) Sum.inl (matrix κ n I B))
        (ScalarIndependentChartPresentation.quotientEquiv R κ n I B a b
          (original R κ n B a b q)) := by
  change IsLocalization.map
    (M := ScalarIndependentChartPresentation.complementMonoid R κ n I B a b)
    (T := ScalarIndependentChartPresentation.newComplementMonoid R κ n I B a b)
    (Localization (M := ScalarIndependentChartPresentation.NewPresentation R κ n I B a b)
      (ScalarIndependentChartPresentation.newComplementMonoid R κ n I B a b))
    (ScalarIndependentChartPresentation.quotientEquiv R κ n I B a b).toRingHom
    (by
      intro q hq
      change ScalarIndependentChartPresentation.quotientEquiv R κ n I B a b q ∈
        ScalarIndependentChartPresentation.newComplementMonoid R κ n I B a b
      rw [← ScalarIndependentChartPresentation.map_complementMonoid R κ n I B a b]
      exact ⟨q, hq, rfl⟩)
    (algebraMap (Presentation R κ n B a b)
      (Localization (ScalarIndependentChartPresentation.complementMonoid R κ n I B a b))
      (original R κ n B a b q)) = _
  rw [IsLocalization.map_eq]
  rfl

theorem chartEquiv_selectedCoordinate (i : Selected n I) :
    chartEquiv R κ n I B a b (selectedCoordinate R κ n I B a b i) =
      ScalarActualOpenChart.globalCoordinate R (Selected n I) (Other n I ⊕ κ) (Other n I)
        (ScalarIndependentChartPresentation.newScalar R n I a)
        (ScalarIndependentChartPresentation.newScalar R n I b) Sum.inl (matrix κ n I B) i := by
  change ScalarIndependentChartPresentation.openEquiv R κ n I B a b
    (directEquiv R κ n I B a b (algebraMap (Global R κ n B a b) (BasicOpen R κ n I B a b)
      (algebraMap (Presentation R κ n B a b) (Global R κ n B a b)
        (original R κ n B a b (Sum.inl i.1))))) = _
  rw [← IsScalarTower.algebraMap_apply, AlgEquiv.commutes, presentation_openEquiv_original]
  have hi : originals κ n I (Sum.inl i.1) = Sum.inl i := by
    apply (originals κ n I).symm.injective
    rw [Equiv.symm_apply_apply]
    rfl
  rw [ScalarIndependentChartPresentation.quotientEquiv_original,hi]
  rfl

#print axioms selectedCoordinate
#print axioms presentation_openEquiv_original
#print axioms chartEquiv_selectedCoordinate
end Verification.ScalarIndependentOpenCoordinates
