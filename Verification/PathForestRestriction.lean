/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathForestRestrictionMatrix

/-!
# Path Forest Restriction

The manuscript's path-forest class is hereditary under arbitrary
principal restrictions, including any relabeling of the selected vertices.
-/
noncomputable section
namespace Verification.PathForestRestriction
open Verification.PathForestMatrixPredicate

theorem hereditary {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : IsPathForest n A) (f : Fin k↪Fin n) :
    IsPathForest k (fun i j=>A (f i) (f j)) := by
  rcases hA with ⟨S,fs,hA⟩
  letI := fs
  rcases hA with ⟨m,o,a,e,hA⟩
  let g : Fin k↪PathForestOrientation.Vertex m o := f.trans e.symm.toEmbedding
  have hg := PathForestRestrictionMatrix.restricted m o g a
  have hm : (fun i j=>A (f i) (f j))=(fun i j=>PathForestOrientation.matrix m o a (g i) (g j)) := by
    funext i j
    have h := hA (e.symm (f i)) (e.symm (f j))
    simpa only [Equiv.apply_symm_apply] using h
  rw [hm]
  exact hg

#print axioms hereditary
end Verification.PathForestRestriction
