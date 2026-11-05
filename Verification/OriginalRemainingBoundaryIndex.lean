/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalFreeCoordinateGraph
import Verification.OriginalBoundaryBranches

/-!
# Original Remaining Boundary Index

None of the retained coefficient coordinates is the new boundary
coordinate. Their actual values therefore remain units on the old-coordinate
closed chart, including every frozen coordinate.
-/
noncomputable section
namespace Verification.OriginalRemainingBoundaryIndex
open Verification.IndependentChartIndex Verification.OriginalFreeTorusCoordinates
variable (κ : Type) [Fintype κ] (n : ℕ) (J : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (v : J)

def oldIndex : Other n (J.erase v.val) := ⟨v.val, Finset.not_mem_erase v.val J⟩

variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, FrozenAcyclicCover.earlierWeights κ n B i j = 0 ↔
  FrozenAcyclicCover.laterWeights κ n B i j = 0)
variable (hJ : ExchangeOpenCover.Independent (FrozenAcyclicCover.laterWeights κ n B) J)

include hpos hneg hsupport hJ in
omit [Fintype κ] in
theorem free_boundary : FreeCoordinate κ n (J.erase v.val) B (Sum.inl (oldIndex n J v)) := by
  apply OriginalFreeCoordinateGraph.enlargement_free κ n (J.erase v.val) B hpos hneg hsupport
  simpa only [oldIndex, Finset.insert_erase v.property] using hJ

def embedding (k : RemainingIndex κ n (J.erase v.val) B) : Other n J ⊕ κ := by
  cases hk : k.val with
  | inr c => exact Sum.inr c
  | inl i =>
    refine Sum.inl ⟨i.val, ?_⟩
    intro hi
    have hiv : i.val = v.val := by
      by_contra h
      exact i.property (Finset.mem_erase.mpr ⟨h, hi⟩)
    have he : i = oldIndex n J v := Subtype.ext hiv
    apply k.property
    rw [hk, he]
    exact free_boundary κ n J B v hpos hneg hsupport hJ

omit [Fintype κ] in
theorem embedding_original (k : RemainingIndex κ n (J.erase v.val) B) :
    IndependentChartPresentation.complementEmbedding κ n J
      (embedding κ n J B v hpos hneg hsupport hJ k) =
    IndependentChartPresentation.complementEmbedding κ n (J.erase v.val) k.val := by
  rcases k with ⟨k, hk⟩
  cases k <;> rfl

variable (R : Type) [Field R]

def coordinateUnit (k : RemainingIndex κ n (J.erase v.val) B) :
    (OriginalBoundaryBranches.Ambient R κ n J B v)ˣ :=
  (OriginalBoundaryBranches.complement_unit R κ n J B v
    (embedding κ n J B v hpos hneg hsupport hJ k)).unit

theorem coordinateUnit_val (k : RemainingIndex κ n (J.erase v.val) B) :
    (coordinateUnit κ n J B v hpos hneg hsupport hJ R k :
      OriginalBoundaryBranches.Ambient R κ n J B v) =
    OriginalBoundaryBranches.coordinate R κ n J B v
      (IndependentChartPresentation.complementEmbedding κ n (J.erase v.val) k.val) := by
  rw [coordinateUnit, IsUnit.unit_spec, embedding_original]

#print axioms oldIndex
#print axioms free_boundary
#print axioms embedding
#print axioms embedding_original
#print axioms coordinateUnit
#print axioms coordinateUnit_val
end Verification.OriginalRemainingBoundaryIndex
