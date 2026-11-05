/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalRemainingBoundaryIndex

/-!
# Original Free Boundary Index

Exactly one of the retained free original coordinates is the new
boundary parameter; all others stay in the complementary open set.
-/
noncomputable section
namespace Verification.OriginalFreeBoundaryIndex
open Verification.IndependentChartIndex Verification.OriginalFreeTorusCoordinates
variable (κ : Type) [Fintype κ] (n : ℕ) (J : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (v : J)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, FrozenAcyclicCover.earlierWeights κ n B i j = 0 ↔
  FrozenAcyclicCover.laterWeights κ n B i j = 0)
variable (hJ : ExchangeOpenCover.Independent (FrozenAcyclicCover.laterWeights κ n B) J)

def boundary : FreeIndex κ n (J.erase v.val) B :=
  ⟨Sum.inl (OriginalRemainingBoundaryIndex.oldIndex n J v),
    OriginalRemainingBoundaryIndex.free_boundary κ n J B v hpos hneg hsupport hJ⟩

omit [Fintype κ] in
theorem boundary_original :
    ((GlobalSelectedColumns.rowEquiv κ n (J.erase v.val)).symm
      (boundary κ n J B v hpos hneg hsupport hJ).val).val = Sum.inl v.val := rfl

local notation "b" => boundary κ n J B v hpos hneg hsupport hJ

def complement (k : FreeIndex κ n (J.erase v.val) B) (hne : k ≠ b) : Other n J ⊕ κ := by
  cases hk : k.val with
  | inr c => exact Sum.inr c
  | inl i =>
    refine Sum.inl ⟨i.val, ?_⟩
    intro hi
    have hiv : i.val = v.val := by
      by_contra h
      exact i.property (Finset.mem_erase.mpr ⟨h, hi⟩)
    apply hne
    apply Subtype.ext
    rw [hk]
    exact congrArg Sum.inl (Subtype.ext hiv)

omit [Fintype κ] in
theorem complement_original (k : FreeIndex κ n (J.erase v.val) B) (hne : k ≠ b) :
    IndependentChartPresentation.complementEmbedding κ n J
      (complement κ n J B v hpos hneg hsupport hJ k hne) =
    ((GlobalSelectedColumns.rowEquiv κ n (J.erase v.val)).symm k.val).val := by
  rcases k with ⟨k, hk⟩
  cases k <;> rfl

#print axioms boundary
#print axioms boundary_original
#print axioms complement
#print axioms complement_original
end Verification.OriginalFreeBoundaryIndex
