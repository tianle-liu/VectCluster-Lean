/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalRostComponentTerms
import Verification.RostComponentEvaluation

/-!
# Original Rost Component Values

Numerical values of the repaired component comparison. The chosen
objects are actual domain factors and ring maps, so generic evaluation
applies without a new compatibility input for the original strata.
-/
noncomputable section
namespace Verification.OriginalRostComponentValues
set_option synthInstance.maxHeartbeats 100000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
open Verification.IndependentChartIndex
variable (T : RostAffineInput.Theory) (F : RostFiniteProducts.Standard T)
variable (S : RostSupportInput.Theory T)
variable (R κ : Type) [Field R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j,earlierWeights κ n B i j=0 ↔ laterWeights κ n B i j=0)
variable (hf : ∀ I,Independent (laterWeights κ n B) I → Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (htame : ∀ I,Independent (laterWeights κ n B) I →
  ∃ (m : ℕ) (sm : Basis.SmithNormalForm (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I))
    (Other n I⊕κ) m),∀ i,IsUnit ((sm.a i).natAbs : R))



variable (Z : RostWeightZero.IntegralConvention T)
variable (E : RostCanonicalCoefficients.GenericZeroEvaluation T F Z)
variable (I : Finset (Fin n)) (hI : Independent (laterWeights κ n B) I)
local notation "D" => OriginalRostComponentTerms.decomposition R κ n B hpos hneg hsupport hf htame I hI

def point (j : (D).Index) : PrimeSpectrum (GlobalNormalFrame.ZeroLayer R κ n I B) :=
  RostComponentEvaluation.point (D).Factor (D).equiv j

theorem point_minimal (j : (D).Index) :
    (point R κ n B hpos hneg hsupport hf htame I hI j).asIdeal ∈
      minimalPrimes (GlobalNormalFrame.ZeroLayer R κ n I B) :=
  RostComponentEvaluation.point_minimal (D).Factor (D).equiv j

theorem stratum_value (j : (D).Index)
    (a : RostCanonicalCoefficients.Sections T (GlobalNormalFrame.ZeroLayer R κ n I B) 0) :
    (OriginalRostComponentTerms.stratumComponents T F R κ n B hpos hneg hsupport hf htame Z I hI).hom a
      (ConnectedComponents.mk (point R κ n B hpos hneg hsupport hf htame I hI j)) =
    E.value (GlobalNormalFrame.ZeroLayer R κ n I B)
      (point R κ n B hpos hneg hsupport hf htame I hI j)
      (point_minimal R κ n B hpos hneg hsupport hf htame I hI j) a :=
  (RostComponentEvaluation.component_value T F Z E (D).Factor (D).equiv j a).symm

#print axioms point
#print axioms point_minimal
#print axioms stratum_value
end Verification.OriginalRostComponentValues
