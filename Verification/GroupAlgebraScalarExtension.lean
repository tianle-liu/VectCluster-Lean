/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Group Algebra Scalar Extension

Scalar extension of a group-algebra basis, retaining each monomial.
-/
noncomputable section
open scoped Classical
namespace Verification.GroupAlgebraScalarExtension
open scoped TensorProduct
variable {G M A : Type*} [AddCommGroup M] [AddCommGroup A]

def equiv (e : M ≃ₗ[ℤ] (G →₀ ℤ)) : M ⊗[ℤ] A ≃ₗ[ℤ] (G →₀ A) :=
  (e.rTensor A).trans (TensorProduct.finsuppScalarLeft ℤ A G)

theorem single (e : M ≃ₗ[ℤ] (G →₀ ℤ)) (m : M) (g : G) (s : ℤ)
    (he : e m = Finsupp.single g s) (a : A) :
    equiv e (m ⊗ₜ[ℤ] a) = Finsupp.single g (s • a) := by
  classical
  change TensorProduct.finsuppScalarLeft ℤ A G (e m ⊗ₜ[ℤ] a) = _
  rw [he]
  ext j
  rw [TensorProduct.finsuppScalarLeft_apply_tmul_apply]
  by_cases h : g=j
  · subst j; simp
  · simp [Finsupp.single_eq_of_ne h]

variable [Monoid G]

theorem scalar_monomial (s : ℤ) (g : G) :
    algebraMap ℤ (MonoidAlgebra ℤ G) s * MonoidAlgebra.of ℤ G g = Finsupp.single g s := by
  change (s : MonoidAlgebra ℤ G) * MonoidAlgebra.single g 1 = _
  simp [MonoidAlgebra.intCast_def,MonoidAlgebra.single_mul_single]

#print axioms equiv
#print axioms single
#print axioms scalar_monomial
end Verification.GroupAlgebraScalarExtension
