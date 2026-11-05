/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathPresentation

/-!
# Path Empty Algebra

The literal path presentation with no mutable vertices is its ground ring.
-/
noncomputable section
namespace Verification.PathEmptyAlgebra
open Verification.PathPresentation
variable (R : Type*) [CommRing R] (a b : R)

def equivalence : PathAlgebra 0 a b ≃ₐ[R] R :=
  AlgEquiv.ofAlgHom (lift a b (fun i : Fin 0=>Fin.elim0 i) (fun i=>Fin.elim0 i)
      (fun i=>Fin.elim0 i)) (Algebra.ofId R _)
    (by apply AlgHom.ext;intro r;exact AlgHom.commutes _ r)
    (by apply hom_ext; all_goals intro i; exact Fin.elim0 i)

#print axioms equivalence
end Verification.PathEmptyAlgebra
