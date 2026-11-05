/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PartialPowerSmooth

/-!
# Partial Power Reindex

Changing the labels of the constrained equations preserves the actual
ideal. This also permits universe-correct finite power-factor constructions.
-/
namespace Verification.PartialPowerReindex
universe u v w
variable {R ι : Type u} {κ : Type v} {κ' : Type w} [CommRing R]
open Verification.PartialPowerSmooth

def reindexEmbedding (j : κ ↪ ι) (q : κ' ≃ κ) : κ' ↪ ι := q.toEmbedding.trans j

theorem reindex_relations (j : κ ↪ ι) (e : κ → ℕ) (b : κ → Rˣ) (q : κ' ≃ κ) :
    relations j e b = relations (reindexEmbedding j q) (e ∘ q) (b ∘ q) := by
  unfold relations
  apply congrArg Ideal.span
  ext p
  constructor
  · rintro ⟨k,rfl⟩
    refine ⟨q.symm k, ?_⟩
    simp [reindexEmbedding]
  · rintro ⟨k,rfl⟩
    exact ⟨q k,rfl⟩

noncomputable def reindexEquiv (j : κ ↪ ι) (e : κ → ℕ) (b : κ → Rˣ) (q : κ' ≃ κ) :
    PartialAlgebra j e b ≃ₐ[R]
      PartialAlgebra (reindexEmbedding j q) (e ∘ q) (b ∘ q) :=
  Ideal.quotientEquivAlgOfEq R (reindex_relations j e b q)

theorem reindex_range (j : κ ↪ ι) (q : κ' ≃ κ) :
    Set.range (reindexEmbedding j q) = Set.range j := by
  change Set.range (j ∘ q) = _
  rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ]

#print axioms reindexEmbedding
#print axioms reindex_relations
#print axioms reindexEquiv
#print axioms reindex_range
end Verification.PartialPowerReindex
