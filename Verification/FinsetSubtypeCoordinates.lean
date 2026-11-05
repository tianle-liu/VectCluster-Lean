/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Data.Finset.Image
import Mathlib.Logic.Equiv.Basic

/-!
# Finset Subtype Coordinates

Finite subsets of a subtype are the finite subsets whose elements
satisfy its predicate, retaining the actual map to the ambient type.
-/
noncomputable section
open scoped Classical
namespace Verification.FinsetSubtypeCoordinates
variable {α : Type*} (P : α → Prop)

def equiv : Finset {a : α // P a} ≃ {S : Finset α // ∀ a ∈ S, P a} where
  toFun S := ⟨S.map (Function.Embedding.subtype P),fun _ h => S.property_of_mem_map_subtype h⟩
  invFun S := S.val.subtype P
  left_inv S := by
    apply Finset.map_injective (Function.Embedding.subtype P)
    exact Finset.subtype_map_of_mem (fun _ h => S.property_of_mem_map_subtype h)
  right_inv S := Subtype.ext (Finset.subtype_map_of_mem S.property)

#print axioms equiv
end Verification.FinsetSubtypeCoordinates
