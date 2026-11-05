/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SmithChainBlock
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Smith Scalar Extension

The actual base-changed Smith bases diagonalize h times the extended
integer/PID differential. This is valid for every commutative coefficient
algebra, including the ring Z[h]/(h²-2h); no flatness is needed.
-/

noncomputable section
namespace Verification.SmithScalarExtension
open scoped TensorProduct
open Verification.SmithChainBlock

variable {R M N : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
variable [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]
variable (S : Type*) [CommRing S] [Algebra R S] (h : S) (d : M →ₗ[R] N)

/-- The independently defined scalar extension of the original differential. -/
def extended : S ⊗[R] M →ₗ[S] S ⊗[R] N :=
  h • TensorProduct.AlgebraTensorModule.map (LinearMap.id : S →ₗ[S] S) d

/-- Base change preserves the actual zero columns. -/
theorem extended_kernel (i : Fin (Module.finrank R (LinearMap.ker d))) :
    extended S h d ((sourceBasis d).baseChange S (Sum.inl i)) = 0 := by
  simp [extended, sourceBasis_kernel]

/-- The scalar on each actual base-changed Smith pair is h times its integral coefficient. -/
theorem extended_pair (i : Fin (smithRank d)) :
    extended S h d ((sourceBasis d).baseChange S (Sum.inr i)) =
      (h * algebraMap R S ((smith d).a i)) •
        (targetBasis d).baseChange S ((smith d).f i) := by
  simp only [extended, LinearMap.smul_apply, Basis.baseChange_apply,
    TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply, sourceBasis_pair]
  rw [TensorProduct.tmul_smul, ← IsScalarTower.algebraMap_smul S ((smith d).a i), smul_smul]

#print axioms extended
#print axioms extended_kernel
#print axioms extended_pair

end Verification.SmithScalarExtension
