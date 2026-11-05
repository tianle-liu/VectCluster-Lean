/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathForestRestrictionCoordinates

/-!
# Path Forest Restriction Matrix

Every entry of a restricted signed path-forest matrix agrees with its
new interval coordinates; in particular no edge is introduced between runs.
-/
noncomputable section
namespace Verification.PathForestRestrictionMatrix
open Classical Verification.PathForestOrientation
open Verification.PathForestRestrictionCoordinates
variable {S : Type} [Fintype S] (m : S→ℕ) (o : S→Bool)
variable {k : ℕ} (f : Fin k↪Vertex m o) (a : S→ℕ→ℤˣ)

omit [Fintype S] in
theorem entry (u v : Vertex (halves m o f) (odd m o f)) :
    matrix m o a (f (PathForestRestrictionCoordinates.reindex m o f u))
      (f (PathForestRestrictionCoordinates.reindex m o f v))=
      matrix (halves m o f) (odd m o f) (signs m o f a) u v := by
  letI : DecidableEq (Index m o f) := Classical.decEq _
  rcases u with ⟨⟨s,c⟩,i⟩
  rcases v with ⟨⟨t,d⟩,j⟩
  rw [reindex_apply,reindex_apply]
  unfold matrix
  by_cases hst : s=t
  · subst t
    by_cases hcd : c=d
    · subst d
      rw [Matrix.blockDiagonal'_apply_eq,Matrix.blockDiagonal'_apply_eq]
      exact local_matrix m o f a ⟨s,c⟩ i j
    · have hsigma : (⟨s,c⟩ : Index m o f)≠⟨s,d⟩ := by
        intro h
        apply hcd
        simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using h
      rw [Matrix.blockDiagonal'_apply_eq,Matrix.blockDiagonal'_apply_ne _ _ _ hsigma]
      apply PathOrientationSigns.matrix_nonedge
      · intro h
        exact hcd (SelectedPathIntervals.component_eq_of_consecutive (selected m o f s)
          (enumerate m o f ⟨s,c⟩ i) (enumerate m o f ⟨s,d⟩ j) h)
      · intro h
        exact hcd (SelectedPathIntervals.component_eq_of_consecutive (selected m o f s)
          (enumerate m o f ⟨s,d⟩ j) (enumerate m o f ⟨s,c⟩ i) h).symm
  · have hsigma : (⟨s,c⟩ : Index m o f)≠⟨t,d⟩ := fun h=>hst (congrArg Sigma.fst h)
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hst,Matrix.blockDiagonal'_apply_ne _ _ _ hsigma]

theorem restricted : PathForestMatrixPredicate.IsPathForest k (fun i j=>matrix m o a (f i) (f j)) := by
  refine ⟨Index m o f,inferInstance,halves m o f,odd m o f,signs m o f a,
    PathForestRestrictionCoordinates.reindex m o f,?_⟩
  exact entry m o f a

#print axioms entry
#print axioms restricted
end Verification.PathForestRestrictionMatrix
