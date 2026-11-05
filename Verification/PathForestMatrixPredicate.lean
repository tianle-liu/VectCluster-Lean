/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathForestOrientation

/-!
# Path Forest Matrix Predicate

The path-forest predicate depends only on the principal matrix. Its
witnesses are actual component coordinates and signed single-arrow entries.
-/
namespace Verification.PathForestMatrixPredicate

def IsPathForest (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∃(S : Type) (f : Fintype S), letI := f
    ∃(m : S→ℕ) (o : S→Bool) (a : S→ℕ→ℤˣ)
      (e : Verification.PathForestOrientation.Vertex m o≃Fin n),
      ∀i j,A (e i) (e j)=Verification.PathForestOrientation.matrix m o a i j

#print axioms IsPathForest
end Verification.PathForestMatrixPredicate
