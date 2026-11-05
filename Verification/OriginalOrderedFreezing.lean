/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarOrderedFreezing
import Verification.OriginalScalarOne

/-!
# Original Ordered Freezing

Ordered freezing on the literal original exchange ring.
-/
noncomputable section
namespace Verification.OriginalOrderedFreezing
open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
open Verification.StrictCohomologicalDimension
universe u
variable {M : Type u} (T : StrictNisnevichInput.Theory M)
variable (R : Type) [Field R] (N : StrictNisnevichInput.Standard T R)
variable (L : StrictPrincipalLongExact.Standard T R)
variable (C : ∀ n : ℕ, (Fin n → Fin n → ℤ) → Prop)
variable (hC : ∀ (κ : Type) [Fintype κ] (n : ℕ)
  (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (a b : Fin n → Rˣ),
  (∀ s i : Fin n, ¬ s < i → (B (Sum.inl s) (Sum.inl i)).toNat=0) →
  (∀ s i : Fin n, ¬ i < s → (-B (Sum.inl s) (Sum.inl i)).toNat=0) →
  (∀ i j, earlierWeights κ n B i j=0 ↔ laterWeights κ n B i j=0) →
  (∀ I : Finset (Fin n), Independent (laterWeights κ n B) I →
    AnticliqueSubcolumns.AS (fun r i => B r (Sum.inl i)) I) →
  C n (fun i j => B (Sum.inl i) (Sum.inl j)) →
  Bound T (ScalarFrozenGlobal.Global R κ n B a b) 0)

include N L hC in
theorem bound (n : ℕ) (κ : Type) [Fintype κ]
    (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
    (hpos : ∀ s i : Fin n, ¬ s < i → (B (Sum.inl s) (Sum.inl i)).toNat=0)
    (hneg : ∀ s i : Fin n, ¬ i < s → (-B (Sum.inl s) (Sum.inl i)).toNat=0)
    (hsupport : ∀ i j, earlierWeights κ n B i j=0 ↔ laterWeights κ n B i j=0)
    (hall : ∀ I : Finset (Fin n), Independent (laterWeights κ n B) I →
      AnticliqueSubcolumns.AS (fun r i => B r (Sum.inl i)) I)
    (rank : Fin n → ℕ) (hinj : Function.Injective rank)
    (horder : FreezingOrder.Good C (fun i j => B (Sum.inl i) (Sum.inl j))
      (ExchangeRing.Adjacent (laterWeights κ n B)) rank) :
    Bound T (Global R κ n B) 1 := by
  exact of_equiv T (OriginalScalarOne.globalEquiv R κ n B).toRingEquiv 1
    (ScalarOrderedFreezing.bound T R N L C hC n κ B (fun _=>1) (fun _=>1)
      hpos hneg hsupport hall rank hinj horder)

#print axioms bound
end Verification.OriginalOrderedFreezing
