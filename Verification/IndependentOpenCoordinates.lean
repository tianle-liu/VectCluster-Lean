/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GlobalExchangeSmooth

/-!
# Independent Open Coordinates

The equivalence from a principal open of the fixed global exchange
presentation to its selected chart preserves the original x coordinates.
-/
noncomputable section
namespace Verification.IndependentOpenCoordinates
open Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.IndependentBasicOpen
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ) (I : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
attribute [local instance] MvPolynomial.algebraMvPolynomial

def selectedCoordinate (i : Selected n I) : BasicOpen R κ n I B :=
  algebraMap (Global R κ n B) (BasicOpen R κ n I B) (initial R κ n B (Sum.inl i.1))

theorem presentation_openEquiv_original (a : Fin n ⊕ κ) :
    IndependentChartPresentation.openEquiv R κ n I B
      (algebraMap (PolynomialPresentation R κ n B)
        (Localization (IndependentChartPresentation.complementMonoid R κ n I B))
        (FrozenOpenChart.original R (Fin n) κ Empty (noMutable κ) B a)) =
      algebraMap (IndependentChartPresentation.NewPresentation R κ n I B)
        (ActualOpenChart.GlobalOpen R (Selected n I) (Other n I ⊕ κ) (Other n I)
          Sum.inl (matrix κ n I B))
        (FrozenOpenChart.original R (Selected n I) (Other n I ⊕ κ) (Other n I)
          Sum.inl (matrix κ n I B) (originals κ n I a)) := by
  change IsLocalization.map
    (M := IndependentChartPresentation.complementMonoid R κ n I B)
    (T := FrozenOpenChart.complementMonoid R (Selected n I) (Other n I ⊕ κ) (Other n I)
      Sum.inl (matrix κ n I B))
    (Localization (M := IndependentChartPresentation.NewPresentation R κ n I B)
      (FrozenOpenChart.complementMonoid R (Selected n I) (Other n I ⊕ κ) (Other n I)
        Sum.inl (matrix κ n I B)))
    (IndependentChartPresentation.quotientEquiv R κ n I B).toRingHom
    (by
      intro q hq
      change IndependentChartPresentation.quotientEquiv R κ n I B q ∈
        FrozenOpenChart.complementMonoid R (Selected n I) (Other n I ⊕ κ) (Other n I)
          Sum.inl (matrix κ n I B)
      rw [← IndependentChartPresentation.map_complementMonoid R κ n I B]
      exact ⟨q, hq, rfl⟩)
    (algebraMap (PolynomialPresentation R κ n B)
      (Localization (IndependentChartPresentation.complementMonoid R κ n I B))
      (FrozenOpenChart.original R (Fin n) κ Empty (noMutable κ) B a)) = _
  rw [IsLocalization.map_eq]
  exact congrArg _ (IndependentChartPresentation.quotientEquiv_original R κ n I B a)

theorem chartEquiv_selectedCoordinate (i : Selected n I) :
    chartEquiv R κ n I B (selectedCoordinate R κ n I B i) =
      ActualOpenChart.globalCoordinate R (Selected n I) (Other n I ⊕ κ) (Other n I)
        Sum.inl (matrix κ n I B) i := by
  change IndependentChartPresentation.openEquiv R κ n I B
    (directEquiv R κ n I B (algebraMap (Global R κ n B) (BasicOpen R κ n I B)
      (algebraMap (PolynomialPresentation R κ n B) (Global R κ n B)
        (FrozenOpenChart.original R (Fin n) κ Empty (noMutable κ) B (Sum.inl i.1))))) = _
  rw [← IsScalarTower.algebraMap_apply, AlgEquiv.commutes, presentation_openEquiv_original]
  have hi : originals κ n I (Sum.inl i.1) = Sum.inl i := by
    apply (originals κ n I).symm.injective
    rw [Equiv.symm_apply_apply]
    rfl
  rw [hi]
  rfl

#print axioms selectedCoordinate
#print axioms presentation_openEquiv_original
#print axioms chartEquiv_selectedCoordinate
end Verification.IndependentOpenCoordinates
