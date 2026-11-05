/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathRootedForest
import Verification.RootedForestDisjoint
import Verification.PathForestOrientation
import Verification.PathForestComponentPresentation

/-!
# Path Forest Rooted Certificate

The actual signed path-forest matrix is a uniform rooted forest and has
exactly the edge weights of its linearly oriented target.
-/
noncomputable section
namespace Verification.PathForestRootedCertificate
open Classical Verification.RootedForestCertificate Verification.PathForestOrientation
variable {S : Type} [Fintype S] (m : S→ℕ) (o : S→Bool)
def shape : Forest (Vertex m o) :=
  Forest.disjoint (fun s=>PathRootedForest.path (PathOrientationBlocks.length (m s) (o s)))

omit [Fintype S] in
theorem support (a : S→ℕ→ℤˣ) (i j : Vertex m o) :
    matrix m o a i j≠0 ↔ (shape m o).Adj i j := by
  rcases i with ⟨s,i⟩
  rcases j with ⟨t,j⟩
  by_cases h : s=t
  · subst t
    rw [matrix,Matrix.blockDiagonal'_apply_eq]
    change _ ↔ (Forest.disjoint (fun s=>PathRootedForest.path (PathOrientationBlocks.length (m s) (o s)))).Adj ⟨s,i⟩ ⟨s,j⟩
    rw [RootedForestDisjoint.same_adj]
    exact PathRootedForest.support (a s) _ i j
  · rw [matrix,Matrix.blockDiagonal'_apply_ne _ _ _ h]
    exact iff_of_false (by simp) (RootedForestDisjoint.different_adj (fun s=>PathRootedForest.path (PathOrientationBlocks.length (m s) (o s))) s t h i j)

omit [Fintype S] in
theorem skew (a : S→ℕ→ℤˣ) (i j : Vertex m o) :
    matrix m o a i j= -matrix m o a j i := by
  rcases i with ⟨s,i⟩
  rcases j with ⟨t,j⟩
  by_cases h : s=t
  · subst t
    rw [matrix,Matrix.blockDiagonal'_apply_eq,Matrix.blockDiagonal'_apply_eq]
    exact PathRootedForest.skew (a s) _ i j
  · rw [matrix,Matrix.blockDiagonal'_apply_ne _ _ _ h,Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm h)]
    simp

omit [Fintype S] in
theorem absolute (a : S→ℕ→ℤˣ) (i j : Vertex m o) :
    |matrix m o a i j|=|PathForestComponentPresentation.blockMatrix m o i j| := by
  rcases i with ⟨s,i⟩
  rcases j with ⟨t,j⟩
  by_cases h : s=t
  · subst t
    rw [matrix,PathForestComponentPresentation.blockMatrix,
      Matrix.blockDiagonal'_apply_eq,Matrix.blockDiagonal'_apply_eq]
    exact PathRootedForest.absolute (a s) _ i j
  · rw [matrix,PathForestComponentPresentation.blockMatrix,
      Matrix.blockDiagonal'_apply_ne _ _ _ h,Matrix.blockDiagonal'_apply_ne _ _ _ h]

#print axioms shape
#print axioms support
#print axioms skew
#print axioms absolute
end Verification.PathForestRootedCertificate
