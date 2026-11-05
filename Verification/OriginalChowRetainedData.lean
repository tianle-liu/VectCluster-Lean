/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalChowExponentFamily

/-!
# Original Chow Retained Data

Retained product data for every allowed original stratum, obtained
from the given tame selected-column ranks. No additional decomposition
hypothesis is required in the final Chow formula.
-/
noncomputable section
namespace Verification.OriginalChowRetainedData
open Verification.IndependentChartIndex Verification.FrozenAcyclicCover
variable (R κ : Type) [Field R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hf : ∀ I, ExchangeOpenCover.Independent (laterWeights κ n B) I →
  Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (htame : ∀ I, ExchangeOpenCover.Independent (laterWeights κ n B) I →
  ∃ (m : ℕ) (sm : Basis.SmithNormalForm
    (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)) (Other n I ⊕ κ) m),
    ∀ i, IsUnit ((sm.a i).natAbs : R))

def data (I : Finset (Fin n)) (hI : ExchangeOpenCover.Independent (laterWeights κ n B) I) :
    OriginalRetainedProductCoordinates.ProductData R κ n I B :=
  Classical.choice (by
    obtain ⟨m,sm,he⟩ := htame I hI
    exact ⟨OriginalRetainedProductCoordinates.decomposition R κ n I B (hf I hI) sm he⟩)

def family (p : ℕ)
    (I : AllowedComponentRow.Source (ExchangeOpenCover.Independent (laterWeights κ n B)) p) :
    OriginalRetainedProductCoordinates.ProductData R κ n I.val B :=
  data R κ n B hf htame I.val I.property.2

#print axioms data
#print axioms family
end Verification.OriginalChowRetainedData
