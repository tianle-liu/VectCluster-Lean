/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GlobalRegularParameters
import Verification.RegularOpenCover

/-!
# Original Rank Nonzerodivisors

Full rank of each independent column collection already makes every
original mutable coordinate a nonzerodivisor in the actual global ring.
No saturation or tameness is needed: regularity on selected charts and
invertibility on complementary charts glue along the actual open cover.
-/
noncomputable section
namespace Verification.OriginalRankNonzerodivisors
open Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.ExchangeOpenCover Verification.IndependentBasicOpen
open Verification.IndependentOpenCoordinates RingTheory.Sequence
variable (R κ : Type) [CommRing R] [Nontrivial R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)

include hpos hneg hsupport in
theorem on_chart (I : Finset (Fin n)) (hI : Independent (laterWeights κ n B) I)
    (hf : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I)) (v : Fin n) :
    IsSMulRegular (BasicOpen R κ n I B)
      (algebraMap (Global R κ n B) (BasicOpen R κ n I B)
        (initial R κ n B (Sum.inl v))) := by
  by_cases hv : v ∈ I
  · have hr := GlobalRegularParameters.selected_coordinates_regular R κ n B
      hpos hneg hsupport I hI hf [⟨v,hv⟩] (by simp)
    have hw := hr.toIsWeaklyRegular
    rw [List.map_singleton, isWeaklyRegular_singleton_iff] at hw
    exact hw
  · exact (complement_units R κ n I B (Sum.inl ⟨v,hv⟩)).isSMulRegular _

include hpos hneg hsupport in
theorem coordinate_regular
    (hf : ∀ I, Independent (laterWeights κ n B) I →
      Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I)) (v : Fin n) :
    IsSMulRegular (Global R κ n B) (initial R κ n B (Sum.inl v)) := by
  apply RegularOpenCover.of_family
    (fun I : {I : Finset (Fin n) // Independent (laterWeights κ n B) I} => chartValue R κ n I.val B)
  · exact chartElements_span_top (laterWeights κ n B)
      (fun i => initial R κ n B (Sum.inl i))
      (ExchangeRing.adjacent_span_eq_top (earlierWeights κ n B) (laterWeights κ n B)
        (fun i => initial R κ n B (Sum.inl i)) (mutated R κ n B)
        (earlierCoefficient R κ n B) (laterCoefficient R κ n B)
        hsupport (earlierCoefficient_unit R κ n B) (ordered_equations R κ n B hpos hneg))
  · intro I
    exact on_chart R κ n B hpos hneg hsupport I.val I.property (hf I.val I.property) v

#print axioms on_chart
#print axioms coordinate_regular
end Verification.OriginalRankNonzerodivisors
