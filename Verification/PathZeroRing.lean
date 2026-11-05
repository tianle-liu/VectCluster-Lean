/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathPresentation

/-!
# Path Zero Ring

The zero-vertex path has exactly its coefficient algebra.
-/
noncomputable section
namespace Verification.PathZeroRing
open Verification.PathPresentation
variable {R : Type*} [CommRing R] (a b : R)

def emptyMap : PathAlgebra 0 a b →ₐ[R] R :=
  PathPresentation.lift a b Fin.elim0 Fin.elim0 (fun i => Fin.elim0 i)

def emptyEquiv : PathAlgebra 0 a b ≃ₐ[R] R :=
  AlgEquiv.ofAlgHom (emptyMap a b) (Algebra.ofId R (PathAlgebra 0 a b))
    (Subsingleton.elim _ _)
    (by
      apply PathPresentation.hom_ext
      · intro i; exact Fin.elim0 i
      · intro i; exact Fin.elim0 i)

#print axioms emptyMap
#print axioms emptyEquiv
end Verification.PathZeroRing
