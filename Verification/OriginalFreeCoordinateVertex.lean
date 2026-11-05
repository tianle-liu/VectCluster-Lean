/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalFreeBoundaryIndex

/-!
# Original Free Coordinate Vertex

Read the original mutable vertex of a free Laurent coordinate. Frozen
coordinates belong to the coefficient ring and are excluded by definition.
-/
noncomputable section
namespace Verification.OriginalFreeCoordinateVertex
open Verification.IndependentChartIndex Verification.OriginalFreeTorusCoordinates
variable (κ : Type) (n : ℕ) (I : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)

def vertex (k : FreeIndex κ n I B) : Fin n := by
  cases hk : k.val with
  | inl i => exact i.val
  | inr c => exact False.elim (by simpa only [hk, FreeCoordinate] using k.property)

theorem original_vertex (k : FreeIndex κ n I B) :
    ((GlobalSelectedColumns.rowEquiv κ n I).symm k.val).val =
      Sum.inl (vertex κ n I B k) := by
  rcases k with ⟨k,hk⟩
  cases k with
  | inl i => rfl
  | inr c => exact hk.elim

theorem vertex_injective : Function.Injective (vertex κ n I B) := by
  intro k l h
  apply Subtype.ext
  apply (GlobalSelectedColumns.rowEquiv κ n I).symm.injective
  apply Subtype.ext
  rw [original_vertex, original_vertex, h]

variable (J : Finset (Fin n)) (v : J)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, FrozenAcyclicCover.earlierWeights κ n B i j = 0 ↔
  FrozenAcyclicCover.laterWeights κ n B i j = 0)
variable (hJ : ExchangeOpenCover.Independent (FrozenAcyclicCover.laterWeights κ n B) J)

theorem boundary_vertex : vertex κ n (J.erase v.val) B
    (OriginalFreeBoundaryIndex.boundary κ n J B v hpos hneg hsupport hJ) = v.val := rfl

#print axioms vertex
#print axioms original_vertex
#print axioms vertex_injective
#print axioms boundary_vertex
end Verification.OriginalFreeCoordinateVertex
