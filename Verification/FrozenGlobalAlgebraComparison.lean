/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FrozenExchangeReindex
import Verification.FrozenGlobalSmooth

/-!
# Frozen Global Algebra Comparison

The generic finite-index frozen presentation and the original Fin-index
presentation have identical ring operations and identical ground scalars.
-/
noncomputable section
namespace Verification.FrozenGlobalAlgebraComparison
variable (R F : Type) [CommRing R] [Fintype F] (n : ℕ)
variable (B : Matrix (Fin n⊕F) (Fin n⊕Empty) ℤ)
def equiv : FrozenAcyclicCover.Global R F n B ≃ₐ[R] FrozenExchangeReindex.Global R B where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
#print axioms equiv
end Verification.FrozenGlobalAlgebraComparison
