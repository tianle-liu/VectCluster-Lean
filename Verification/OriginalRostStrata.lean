/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RostFiniteProducts
import Verification.IndependentStratumCoordinates

/-!
# Original Rost Strata

The arbitrary-field tame-rank stratum acyclicity statement on the
literal original zero-layer rings. Smith splitting and all coordinate
changes are derived from the original columns, not supplied as geometry.
-/
noncomputable section
namespace Verification.OriginalRostStrata
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
open Verification.IndependentChartIndex
variable (T : RostAffineInput.Theory) (F : RostFiniteProducts.Standard T)
variable (R κ : Type) [Field R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j,earlierWeights κ n B i j=0 ↔ laterWeights κ n B i j=0)
variable (I : Finset (Fin n)) (hI : Independent (laterWeights κ n B) I)
variable (hf : Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable {m : ℕ} (sm : Basis.SmithNormalForm (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)) (Other n I⊕κ) m)
variable (he : ∀ i,IsUnit ((sm.a i).natAbs : R))

include F hpos hneg hsupport hI hf sm he in
theorem positive (s : ℤ) (q : ℕ) (hq : 0<q) :
    IsZero ((T.cycles (Spec (CommRingCat.of (GlobalNormalFrame.ZeroLayer R κ n I B))) s).homology q) := by
  have h := RostFiniteProducts.smith_stratum_positive T F
    (Sum.inl : Other n I→Other n I⊕κ) (matrix κ n I B)
    (IndependentChartIndex.matrix_zero_block κ n I B hpos hneg hsupport hI)
    (GlobalExchangeSmooth.selectedMap κ n B I) Finsupp.basisSingleOne
    (fun i => ActualOpenGeometry.columnMap_single (Selected n I) (Other n I⊕κ) (Other n I) (matrix κ n I B) i)
    hf sm he s q hq
  exact IsZero.of_iso h (T.iso (Scheme.Spec.mapIso
    (IndependentStratumCoordinates.originalStratumEquiv R κ n I B).toCommRingCatIso.symm.op) s q)

#print axioms positive
end Verification.OriginalRostStrata
