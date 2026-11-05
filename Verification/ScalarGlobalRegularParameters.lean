/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarIndependentOpenCoordinates
import Verification.ScalarActualOpenRegular

/-!
# Scalar Global Regular Parameters

The regular normal coordinates live on the actual principal opens of
one fixed frozen global exchange presentation. The coordinate-preserving
chart equivalence transports the proved regular sequence to these opens.
-/
noncomputable section
namespace Verification.ScalarGlobalRegularParameters
open Verification.ScalarFrozenGlobal Verification.IndependentChartIndex
open Verification.FrozenAcyclicCover (earlierWeights laterWeights)
open Verification.ExchangeOpenCover Verification.ScalarIndependentBasicOpen
open Verification.ScalarIndependentOpenCoordinates RingTheory.Sequence
variable (R κ : Type) [CommRing R] [Nontrivial R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (a b : Fin n → Rˣ)
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] RingHomInvPair.of_ringEquiv

theorem selected_coordinates_regular
    (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
    (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
    (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
    (I : Finset (Fin n)) (hI : Independent (laterWeights κ n B) I)
    (hf : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
    (hs : FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)))
    (l : List (Selected n I)) (hl : l.Nodup) :
    IsRegular (BasicOpen R κ n I B a b) (l.map (selectedCoordinate R κ n I B a b)) := by
  let e := (chartEquiv R κ n I B a b).toRingEquiv
  apply (e.toSemilinearEquiv.isRegular_congr' (l.map (selectedCoordinate R κ n I B a b))).mpr
  have hm : (l.map (selectedCoordinate R κ n I B a b)).map e.toRingHom =
      l.map (ScalarActualOpenChart.globalCoordinate R (Selected n I) (Other n I ⊕ κ) (Other n I)
        (ScalarIndependentChartPresentation.newScalar R n I a)
        (ScalarIndependentChartPresentation.newScalar R n I b) Sum.inl (matrix κ n I B)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    exact chartEquiv_selectedCoordinate R κ n I B a b i
  change IsRegular
    (ScalarActualOpenChart.GlobalOpen R (Selected n I) (Other n I ⊕ κ) (Other n I)
      (ScalarIndependentChartPresentation.newScalar R n I a)
      (ScalarIndependentChartPresentation.newScalar R n I b) Sum.inl (matrix κ n I B))
    ((l.map (selectedCoordinate R κ n I B a b)).map e.toRingHom)
  rw [hm]
  exact ScalarActualOpenRegular.coordinates_regular R (Selected n I) (Other n I ⊕ κ)
    (Other n I) (ScalarIndependentChartPresentation.newScalar R n I a)
    (ScalarIndependentChartPresentation.newScalar R n I b) Sum.inl (matrix κ n I B)
    (matrix_zero_block κ n I B hpos hneg hsupport hI) hf hs l hl

#print axioms selected_coordinates_regular
end Verification.ScalarGlobalRegularParameters
