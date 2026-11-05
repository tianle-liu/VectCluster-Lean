/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOrientationBlocks
import Verification.PathForestOriginalRFR

/-!
# Path Forest Orientation

Literal adjacency coordinates for a disjoint union of arbitrarily oriented
single-arrow paths. The matrix identification required by forest RFR is proved
entry by entry, including vanishing between distinct components.
-/
noncomputable section
namespace Verification.PathForestOrientation
open Classical Verification.PathForestMatching Verification.PathForestFullRank
open Verification.PathForestEntries
variable {S : Type} [Fintype S] (m : S → ℕ) (o : S → Bool) (a : S → ℕ → ℤˣ)
abbrev Vertex := Σ s,Fin (PathOrientationBlocks.length (m s) (o s))

def matrix : Matrix (Vertex m o) (Vertex m o) ℤ :=
  Matrix.blockDiagonal' (fun s=>PathOrientationSigns.matrix (a s) (PathOrientationBlocks.length (m s) (o s)))

def leftSigns (s : S) := PathOrientationBlocks.leftSign (a s) (m s) (o s)
def rightSigns (s : S) := PathOrientationBlocks.rightSign (a s) (m s) (o s)

def sides : (PIndex m o ⊕ QIndex m) ≃ (Σ s,largeIndex (m s) (o s) ⊕ Fin (m s)) :=
  (Equiv.sigmaSumDistrib (fun s=>largeIndex (m s) (o s)) (fun s=>Fin (m s))).symm

omit [Fintype S] in
theorem sides_inl (s : S) (i : largeIndex (m s) (o s)) :
    sides m o (Sum.inl ⟨s,i⟩)=⟨s,Sum.inl i⟩ := rfl
omit [Fintype S] in
theorem sides_inr (s : S) (i : Fin (m s)) :
    sides m o (Sum.inr ⟨s,i⟩)=⟨s,Sum.inr i⟩ := rfl

def reindex : (PIndex m o ⊕ QIndex m) ≃ Vertex m o :=
  (sides m o).trans (Equiv.sigmaCongrRight (fun s=>PathOrientationBlocks.reindex (m s) (o s)))

theorem block_coordinates :
    (Matrix.blockDiagonal' (fun s=>PathOrientationBlocks.block (a s) (m s) (o s))).submatrix
      (sides m o) (sides m o)=principal m o (leftSigns m o a) (rightSigns m o a) := by
  ext p q
  rcases p with ⟨s,i⟩ | ⟨s,i⟩ <;> rcases q with ⟨t,j⟩ | ⟨t,j⟩
  all_goals
    simp only [Matrix.submatrix_apply,sides_inl,sides_inr]
    by_cases h : s=t
  all_goals try subst t
  all_goals try rw [Matrix.blockDiagonal'_apply_eq]
  all_goals try rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]
  all_goals simp only [PathOrientationBlocks.block,PathOrientationBlocks.matching,
    principal,Matrix.fromBlocks,Matrix.of_apply,Sum.elim_inl,Sum.elim_inr,
    Matrix.zero_apply,Matrix.neg_apply,Matrix.transpose_apply]
  all_goals try rw [same_component]
  all_goals try rw [different_component m o (leftSigns m o a) (rightSigns m o a) s t h]
  all_goals try rw [different_component m o (leftSigns m o a) (rightSigns m o a) t s (Ne.symm h)]
  all_goals rfl

theorem matrix_reindex : (matrix m o a).submatrix (reindex m o) (reindex m o)=
    principal m o (leftSigns m o a) (rightSigns m o a) := by
  rw [← block_coordinates]
  ext p q
  obtain ⟨⟨s,i⟩,rfl⟩ := (sides m o).symm.surjective p
  obtain ⟨⟨t,j⟩,rfl⟩ := (sides m o).symm.surjective q
  simp only [Matrix.submatrix_apply,reindex,Equiv.trans_apply,Equiv.apply_symm_apply]
  change Matrix.blockDiagonal' (fun s=>PathOrientationSigns.matrix (a s) (PathOrientationBlocks.length (m s) (o s)))
    ⟨s,PathOrientationBlocks.reindex (m s) (o s) i⟩
    ⟨t,PathOrientationBlocks.reindex (m t) (o t) j⟩=
      Matrix.blockDiagonal' (fun s=>PathOrientationBlocks.block (a s) (m s) (o s)) ⟨s,i⟩ ⟨t,j⟩
  by_cases h:s=t
  · subst t
    rw [Matrix.blockDiagonal'_apply_eq,Matrix.blockDiagonal'_apply_eq]
    exact congrFun (congrFun (PathOrientationBlocks.matrix_reindex (a s) (m s) (o s)) i) j
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h,Matrix.blockDiagonal'_apply_ne _ _ _ h]

#print axioms Vertex
#print axioms matrix
#print axioms leftSigns
#print axioms rightSigns
#print axioms sides
#print axioms sides_inl
#print axioms sides_inr
#print axioms reindex
#print axioms block_coordinates
#print axioms matrix_reindex
end Verification.PathForestOrientation
