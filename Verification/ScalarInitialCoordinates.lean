/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarIndependentOpenCoordinates
import Verification.ActualOpenCoefficients

/-!
# Scalar Initial Coordinates

A coordinate-preserving identification of the actual initial open torus.
It is derived from the actual scalar exchange chart, with the empty selected
block; every original coordinate is sent to its displayed Laurent variable.
-/
noncomputable section
namespace Verification.ScalarInitialCoordinates
set_option maxHeartbeats 100000
open MvPolynomial Verification.ScalarFrozenGlobal Verification.IndependentChartIndex
open Verification.ScalarIndependentBasicOpen

def emptyLocalEquiv (S I : Type) [CommRing S] [IsEmpty I] (χ : I → Sˣ) :
    LocalExchangeSmooth.LocalAlgebra χ ≃ₐ[S] S :=
  (Ideal.quotientEquivAlgOfEq S (show LocalExchangeSmooth.relations χ = ⊥ by
    simp [LocalExchangeSmooth.relations, Set.range_eq_empty])).trans
      ((AlgEquiv.quotientBot S _).trans (isEmptyAlgEquiv S (I ⊕ I)))

#print axioms emptyLocalEquiv

variable (R ι κ τ : Type) [CommRing R] [Fintype ι] [Fintype κ]
variable (a b : (ι ⊕ τ) → Rˣ) (j : τ → κ)
variable (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)

theorem scalarChart_outside (hB : ∀ l i : ι, B (Sum.inl l) (Sum.inl i) = 0) (k : κ) :
    ScalarActualOpenChart.globalOpenEquiv R ι κ τ a b j B hB
      (algebraMap (ScalarActualOpenChart.Original R ι κ)
        (ScalarActualOpenChart.GlobalOpen R ι κ τ a b j B) (X (Sum.inr k))) =
      algebraMap (OriginalTorus.Torus R κ)
        (LocalExchangeSmooth.LocalAlgebra (ScalarActualOpenChart.characters R ι κ τ a b B))
          (OriginalTorus.torusCoordinate R κ k) := by
  change ScalarActualOpenChart.localizedChartEquiv R ι κ τ a b j B hB
    ((ScalarActualOpenChart.globalToLocalized R ι κ τ a b j B)
      (algebraMap (ScalarActualOpenChart.Original R ι κ) _ (X (Sum.inr k)))) = _
  rw [AlgEquiv.commutes]
  exact ActualOpenCoefficients.prepared_coefficient
    (PartialOriginalLocalization.openOriginalEquiv R ι κ)
    (ActualOpenChart.localizedInitial R ι κ τ j)
    (ScalarActualOpenChart.localizedExchange R ι κ τ a b B)
    (fun t => PartialOriginalLocalization.coordinateUnits R ι κ (j t))
    (ScalarActualOpenChart.negativeUnits R ι κ τ b B)
    (ScalarActualOpenChart.characters R ι κ τ a b B)
    (ActualOpenChart.localizedInitial_unit R ι κ τ j)
    (ActualOpenChart.localizedInitial_free R ι κ τ j)
    (ScalarActualOpenChart.localizedExchange_free R ι κ τ a b B hB) _ _
    (PartialOriginalLocalization.toTarget_coordinate R ι κ (Sum.inr k))

#print axioms scalarChart_outside

variable (n : ℕ) (I : Finset (Fin n))
variable (M : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (c d : Fin n → Rˣ)
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem chart_outside (q : Other n I ⊕ κ) :
    chartEquiv R κ n I M c d
      (algebraMap (Global R κ n M c d) (BasicOpen R κ n I M c d)
        (initial R κ n M c d (IndependentChartPresentation.complementEmbedding κ n I q))) =
      algebraMap (ScalarActualOpenChart.Original R (Selected n I) (Other n I ⊕ κ))
        (ScalarActualOpenChart.GlobalOpen R (Selected n I) (Other n I ⊕ κ) (Other n I)
          (ScalarIndependentChartPresentation.newScalar R n I c)
          (ScalarIndependentChartPresentation.newScalar R n I d) Sum.inl (matrix κ n I M))
            (X (Sum.inr q)) := by
  change ScalarIndependentChartPresentation.openEquiv R κ n I M c d
    (directEquiv R κ n I M c d (algebraMap (Global R κ n M c d) (BasicOpen R κ n I M c d)
      (algebraMap (Presentation R κ n M c d) (Global R κ n M c d)
        (original R κ n M c d (IndependentChartPresentation.complementEmbedding κ n I q))))) = _
  rw [← IsScalarTower.algebraMap_apply, AlgEquiv.commutes,
    ScalarIndependentOpenCoordinates.presentation_openEquiv_original,
    ScalarIndependentChartPresentation.quotientEquiv_original,
    IndependentChartPresentation.originals_complement]
  rfl

#print axioms chart_outside

instance selectedEmptyIsEmpty : IsEmpty (Selected n ∅) :=
  ⟨fun i => Finset.not_mem_empty i.val i.property⟩

#print axioms selectedEmptyIsEmpty

def coordinateTorusEquiv : BasicOpen R κ n ∅ M c d ≃ₐ[R]
    OriginalTorus.Torus R (Other n ∅ ⊕ κ) :=
  (chartEquiv R κ n ∅ M c d).trans
    ((ScalarActualOpenChart.globalOpenEquiv R (Selected n ∅) (Other n ∅ ⊕ κ) (Other n ∅)
      (ScalarIndependentChartPresentation.newScalar R n ∅ c)
      (ScalarIndependentChartPresentation.newScalar R n ∅ d) Sum.inl (matrix κ n ∅ M)
        (fun l => isEmptyElim l)).trans
      ((emptyLocalEquiv (OriginalTorus.Torus R (Other n ∅ ⊕ κ)) (Selected n ∅)
        (ScalarActualOpenChart.characters R (Selected n ∅) (Other n ∅ ⊕ κ) (Other n ∅)
          (ScalarIndependentChartPresentation.newScalar R n ∅ c)
          (ScalarIndependentChartPresentation.newScalar R n ∅ d) (matrix κ n ∅ M))).restrictScalars R))

#print axioms coordinateTorusEquiv

theorem coordinateTorusEquiv_original (q : Other n ∅ ⊕ κ) :
    coordinateTorusEquiv R κ n M c d
      (algebraMap (Global R κ n M c d) (BasicOpen R κ n ∅ M c d)
        (initial R κ n M c d (IndependentChartPresentation.complementEmbedding κ n ∅ q))) =
      OriginalTorus.torusCoordinate R (Other n ∅ ⊕ κ) q := by
  dsimp only [coordinateTorusEquiv, AlgEquiv.trans_apply]
  rw [chart_outside, scalarChart_outside]
  exact (emptyLocalEquiv (OriginalTorus.Torus R (Other n ∅ ⊕ κ)) (Selected n ∅)
    (ScalarActualOpenChart.characters R (Selected n ∅) (Other n ∅ ⊕ κ) (Other n ∅)
      (ScalarIndependentChartPresentation.newScalar R n ∅ c)
      (ScalarIndependentChartPresentation.newScalar R n ∅ d) (matrix κ n ∅ M))).commutes _

#print axioms coordinateTorusEquiv_original
end Verification.ScalarInitialCoordinates
