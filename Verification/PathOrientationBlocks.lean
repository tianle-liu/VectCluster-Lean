/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathForestEntries

/-!
# Path Orientation Blocks

Exact parity reindexing of a path with arbitrary single-arrow orientations.
The cumulative vertex signs identify its literal adjacency entries with the
signed bipartite matrix used for the forest splitting.
-/
noncomputable section
namespace Verification.PathOrientationBlocks
open Verification.PathForestMatching Verification.PathForestEntries
open Verification.PathOrientationSigns

def length (m : ℕ) : Bool → ℕ
  | false => 2*m
  | true => 2*m+1

def reindex (m : ℕ) (o : Bool) : (largeIndex m o ⊕ Fin m) ≃ Fin (length m o) :=
  match o with
  | false => PathLattice.evenReindex m
  | true => PathLattice.oddReindex m

def leftSign (a : ℕ → ℤˣ) (m : ℕ) (o : Bool) (i : largeIndex m o) : ℤˣ :=
  vertexSign a (reindex m o (Sum.inl i)).val

def rightSign (a : ℕ → ℤˣ) (m : ℕ) (o : Bool) (i : Fin m) : ℤˣ :=
  vertexSign a (reindex m o (Sum.inr i)).val

def matching (a : ℕ → ℤˣ) (m : ℕ) (o : Bool) : Matrix (largeIndex m o) (Fin m) ℤ :=
  fun i j=>(leftSign a m o i : ℤ)*localMatrix m o i j*(rightSign a m o j : ℤ)

def block (a : ℕ → ℤˣ) (m : ℕ) (o : Bool) : Matrix (largeIndex m o ⊕ Fin m) (largeIndex m o ⊕ Fin m) ℤ :=
  Matrix.fromBlocks 0 (matching a m o) (-(matching a m o).transpose) 0

theorem linear_reindex (m : ℕ) (o : Bool) :
    (PathLattice.pathMatrix (length m o)).submatrix (reindex m o) (reindex m o)=
      Matrix.fromBlocks 0 (localMatrix m o) (-(localMatrix m o).transpose) 0 := by
  cases o
  · exact PathLattice.evenMatrix_reindex m
  · exact PathLattice.oddMatrix_reindex m

theorem matrix_reindex (a : ℕ → ℤˣ) (m : ℕ) (o : Bool) :
    (matrix a (length m o)).submatrix (reindex m o) (reindex m o)=block a m o := by
  ext i j
  change matrix a (length m o) (reindex m o i) (reindex m o j)=_
  rw [matrix_conjugacy]
  have h := congrFun (congrFun (linear_reindex m o) i) j
  change PathLattice.pathMatrix (length m o) (reindex m o i) (reindex m o j)=_ at h
  rw [h]
  cases i <;> cases j
  all_goals simp only [block,matching,Matrix.fromBlocks,Matrix.of_apply,Matrix.zero_apply,
    Matrix.neg_apply,Matrix.transpose_apply,Sum.elim_inl,Sum.elim_inr,leftSign,rightSign]
  all_goals ring

#print axioms length
#print axioms reindex
#print axioms leftSign
#print axioms rightSign
#print axioms matching
#print axioms block
#print axioms linear_reindex
#print axioms matrix_reindex
end Verification.PathOrientationBlocks
