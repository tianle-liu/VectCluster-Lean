/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOrientationSigns

/-!
# Single Modified Path

Weighted Dynkin paths (types B, C, F and G) differ from a
single-arrow path only on one edge. Deleting an endpoint of that edge
removes every modified entry, regardless of its two integer weights.
-/
namespace Verification.SingleModifiedPath
variable (n : ℕ) (a : ℕ → ℤˣ) (v : Fin n) (c d : ℤ)

def matrix (i j : Fin n) : ℤ :=
  if i=v ∧ j.val=v.val+1 then c
  else if j=v ∧ i.val=v.val+1 then d
  else PathOrientationSigns.matrix a n i j

theorem unchanged (i j : Fin n) (hi : i≠v) (hj : j≠v) :
    matrix n a v c d i j=PathOrientationSigns.matrix a n i j := by
  simp [matrix,hi,hj]

theorem deleted_matrix {m : ℕ} (f : Fin m ↪ Fin n) (hf : ∀ i,f i≠v) :
    (fun i j => matrix n a v c d (f i) (f j))=
      fun i j => PathOrientationSigns.matrix a n (f i) (f j) := by
  funext i j
  exact unchanged n a v c d (f i) (f j) (hf i) (hf j)

#print axioms matrix
#print axioms unchanged
#print axioms deleted_matrix
end Verification.SingleModifiedPath
