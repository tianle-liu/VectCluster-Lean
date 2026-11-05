/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Data.Fintype.EquivFin

/-!
# Finite Vertex Deletion

Explicit finite enumeration of the complement of one vertex.
-/
noncomputable section
namespace Verification.FiniteVertexDeletion
open Classical
variable (n : ℕ) (v : Fin n)
abbrev Remaining := {w : Fin n // w≠v}
def label : Remaining n v ≃ Fin (Fintype.card (Remaining n v)) := Fintype.equivFin _
def embedding : Fin (Fintype.card (Remaining n v)) ↪ Fin n :=
  ⟨fun i => ((label n v).symm i).val,Subtype.val_injective.comp (label n v).symm.injective⟩

theorem range_iff (w : Fin n) : w∈Set.range (embedding n v) ↔ w≠v := by
  constructor
  · rintro ⟨i,rfl⟩
    exact ((label n v).symm i).property
  · intro hw
    exact ⟨label n v ⟨w,hw⟩,congrArg Subtype.val ((label n v).symm_apply_apply ⟨w,hw⟩)⟩

#print axioms Remaining
#print axioms label
#print axioms embedding
#print axioms range_iff
end Verification.FiniteVertexDeletion
