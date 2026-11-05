/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarGlobalRegularParameters
import Verification.GlobalSelectedColumns
import Verification.RegularOpenCover

/-!
# Scalar Global Nonzerodivisors

Each original mutable coordinate is a nonzerodivisor in the same
actual scalar global ring. The proof glues its regularity on selected
charts and its invertibility on all other charts.
-/
noncomputable section
namespace Verification.ScalarGlobalNonzerodivisors
open Verification.ScalarFrozenGlobal Verification.IndependentChartIndex
open Verification.FrozenAcyclicCover (earlierWeights laterWeights)
open Verification.ExchangeOpenCover Verification.ScalarIndependentBasicOpen
open Verification.ScalarIndependentOpenCoordinates RingTheory.Sequence
variable (R κ : Type) [CommRing R] [Nontrivial R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (a b : Fin n → Rˣ)
variable (hpos : ∀ r i : Fin n, ¬ r < i → (B (Sum.inl r) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ r i : Fin n, ¬ i < r → (-B (Sum.inl r) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
include hpos hneg hsupport

theorem on_chart (I : Finset (Fin n)) (hI : Independent (laterWeights κ n B) I)
    (hAS : AnticliqueSubcolumns.AS (fun q j => B q (Sum.inl j)) I) (v : Fin n) :
    IsSMulRegular (BasicOpen R κ n I B a b)
      (algebraMap (Global R κ n B a b) (BasicOpen R κ n I B a b)
        (initial R κ n B a b (Sum.inl v))) := by
  by_cases hv : v ∈ I
  · obtain ⟨hf,hs⟩ := (GlobalSelectedColumns.AS_iff κ n B I).mpr hAS
    have hr := ScalarGlobalRegularParameters.selected_coordinates_regular R κ n B a b
      hpos hneg hsupport I hI hf hs [⟨v,hv⟩] (by simp)
    have hw := hr.toIsWeaklyRegular
    rw [List.map_singleton,isWeaklyRegular_singleton_iff] at hw
    exact hw
  · exact (complement_units R κ n I B a b (Sum.inl ⟨v,hv⟩)).isSMulRegular _

theorem coordinate_regular
    (hall : ∀ I : Finset (Fin n), Independent (laterWeights κ n B) I →
      AnticliqueSubcolumns.AS (fun q j => B q (Sum.inl j)) I) (v : Fin n) :
    IsSMulRegular (Global R κ n B a b) (initial R κ n B a b (Sum.inl v)) := by
  apply RegularOpenCover.of_family
    (fun I : {I : Finset (Fin n) // Independent (laterWeights κ n B) I} => chartValue R κ n I.1 B a b)
  · exact chartElements_span_top (laterWeights κ n B)
      (fun i => initial R κ n B a b (Sum.inl i))
      (ExchangeRing.adjacent_span_eq_top (earlierWeights κ n B) (laterWeights κ n B)
        (fun i => initial R κ n B a b (Sum.inl i)) (mutated R κ n B a b)
        (earlierCoefficient R κ n B a b) (laterCoefficient R κ n B a b)
        hsupport (earlierCoefficient_unit R κ n B a b) (ordered_equations R κ n B a b hpos hneg))
  · intro I
    exact on_chart R κ n B a b hpos hneg hsupport I.1 I.2 (hall I.1 I.2) v

#print axioms on_chart
#print axioms coordinate_regular
end Verification.ScalarGlobalNonzerodivisors
