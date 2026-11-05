/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.IndependentOpenCoordinates
import Verification.ActualRegularSequence

/-!
# Global Regular Parameters

The regular normal coordinates live on the actual principal opens of
one fixed frozen global exchange presentation. The coordinate-preserving
chart equivalence transports the proved regular sequence to these opens.
-/
noncomputable section
namespace Verification.GlobalRegularParameters
open Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.ExchangeOpenCover Verification.IndependentBasicOpen
open Verification.IndependentOpenCoordinates RingTheory.Sequence
variable (R κ : Type) [CommRing R] [Nontrivial R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] RingHomInvPair.of_ringEquiv

theorem selected_coordinates_regular
    (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
    (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
    (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
    (I : Finset (Fin n)) (hI : Independent (laterWeights κ n B) I)
    (hf : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
    (l : List (Selected n I)) (hl : l.Nodup) :
    IsRegular (BasicOpen R κ n I B) (l.map (selectedCoordinate R κ n I B)) := by
  let e := (chartEquiv R κ n I B).toRingEquiv
  apply (e.toSemilinearEquiv.isRegular_congr' (l.map (selectedCoordinate R κ n I B))).mpr
  have hm : (l.map (selectedCoordinate R κ n I B)).map e.toRingHom =
      l.map (ActualOpenChart.globalCoordinate R (Selected n I) (Other n I ⊕ κ) (Other n I)
        Sum.inl (matrix κ n I B)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    exact chartEquiv_selectedCoordinate R κ n I B i
  change IsRegular
    (ActualOpenChart.GlobalOpen R (Selected n I) (Other n I ⊕ κ) (Other n I)
      Sum.inl (matrix κ n I B))
    ((l.map (selectedCoordinate R κ n I B)).map e.toRingHom)
  rw [hm]
  exact ActualRegularSequence.original_coordinates_regular R (Selected n I) (Other n I ⊕ κ)
    (Other n I) Sum.inl (matrix κ n I B)
    (matrix_zero_block κ n I B hpos hneg hsupport hI) hf l hl

#print axioms selected_coordinates_regular
end Verification.GlobalRegularParameters
