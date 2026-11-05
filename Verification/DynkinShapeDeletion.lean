/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SingleModifiedPath
import Verification.BranchedPathMatrix
import Verification.FiniteVertexDeletion
import Verification.OneVertexFreezingOrder
import Verification.PathForestRestriction
import Verification.PathForestArbitraryLengths

/-!
# Dynkin Shape Deletion

Internal deletion proofs for the finite Dynkin matrix shapes.
Weighted-path and branching entries are actual integer matrices; no
forest-deletion conclusion is imported from finite-type classification.
-/
noncomputable section
namespace Verification.DynkinShapeDeletion
open Classical Verification.PathForestMatrixPredicate

theorem hereditary : OneVertexFreezingOrder.Hereditary IsPathForest :=
  fun _ _ A h f => PathForestRestriction.hereditary A h f

theorem modified_good (n : ℕ) (a : ℕ→ℤˣ) (v : Fin n) (c d : ℤ)
    (E : Fin n → Fin n → Prop) :
    FreezingOrder.Good IsPathForest (SingleModifiedPath.matrix n a v c d) E
      (OneVertexFreezingOrder.rank v) := by
  let f := FiniteVertexDeletion.embedding n v
  have hf := FiniteVertexDeletion.range_iff n v
  have hn : ∀ i,f i≠v := fun i => (hf (f i)).mp ⟨i,rfl⟩
  apply OneVertexFreezingOrder.good IsPathForest v hereditary _ E _ f hf
  rw [SingleModifiedPath.deleted_matrix n a v c d f hn]
  exact PathForestRestriction.hereditary _ (PathForestArbitraryLengths.single n a) f

variable {S : Type} [Fintype S] (length : S→ℕ) (a : S→ℕ→ℤˣ) (up down : S→ℤ)
variable (n : ℕ) (e : BranchedPathMatrix.Vertices length ≃ Fin n)
variable (A : Matrix (Fin n) (Fin n) ℤ)
variable (hA : ∀ i j,A (e i) (e j)=BranchedPathMatrix.matrix length a up down i j)

include hA in
theorem branched_good (E : Fin n → Fin n → Prop) :
    FreezingOrder.Good IsPathForest A E (OneVertexFreezingOrder.rank (e none)) := by
  let b : BranchedPathMatrix.Branches length ≃ Fin (Fintype.card (BranchedPathMatrix.Branches length)) :=
    Fintype.equivFin _
  let f : Fin (Fintype.card (BranchedPathMatrix.Branches length)) ↪ Fin n :=
    b.symm.toEmbedding.trans ((BranchedPathMatrix.deletion length).trans e.toEmbedding)
  have hf : ∀ w,w∈Set.range f ↔ w≠e none := by
    intro w
    constructor
    · rintro ⟨i,rfl⟩ hh
      exact Option.noConfusion (e.injective hh)
    · intro hw
      have hh : e.symm w≠none := fun hh => hw (by rw [←e.apply_symm_apply w,hh])
      obtain ⟨x,hx⟩ := (BranchedPathMatrix.deletion_range length (e.symm w)).mpr hh
      refine ⟨b x,?_⟩
      change e (some (b.symm (b x)))=w
      rw [b.symm_apply_apply]
      exact (congrArg e hx).trans (e.apply_symm_apply w)
  apply OneVertexFreezingOrder.good IsPathForest (e none) hereditary A E _ f hf
  apply PathForestArbitraryLengths.block length a _ b
  intro i j
  change A (e (some (b.symm (b i)))) (e (some (b.symm (b j))))=_
  rw [b.symm_apply_apply,b.symm_apply_apply,hA]
  rfl

#print axioms hereditary
#print axioms modified_good
#print axioms branched_good
end Verification.DynkinShapeDeletion
