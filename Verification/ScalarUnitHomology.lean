/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarBlockTensor

/-!
# Scalar Unit Homology

Unit Smith blocks have zero kernel and cokernel over every coefficient
module. Removing exactly those factors leaves only the unmatched copies.
-/
noncomputable section
namespace Verification.ScalarUnitHomology
variable {R : Type} [CommRing R] (M : Type) [AddCommGroup M] [Module R M]

/-- No torsion assumption on the coefficient module is required. -/
def kernelSubsingleton (a : R) (ha : IsUnit a) :
    Subsingleton (LinearMap.ker (a • (LinearMap.id : M →ₗ[R] M))) := by
  apply (Submodule.subsingleton_iff_eq_bot).mpr
  apply LinearMap.ker_eq_bot.mpr
  exact ha.smul_bijective.injective

def quotientSubsingleton (a : R) (ha : IsUnit a) :
    Subsingleton (M ⧸ LinearMap.range (a • (LinearMap.id : M →ₗ[R] M))) := by
  apply Submodule.subsingleton_quotient_iff_eq_top.mpr
  apply LinearMap.range_eq_top.mpr
  exact ha.smul_bijective.surjective

variable {I K : ℤ → Type} [∀ n, Fintype (I n)] [∀ n, Fintype (K n)]
variable (e : ∀ n, I n ↪ K n) (a : ∀ n, I n → R)

def termsEquiv (n : ℤ) (hin : ∀ i, IsUnit (a n i)) (hout : ∀ i, IsUnit (a (n+1) i)) :
    ScalarBlockComplex.HomologyTerms e (ScalarBlockTensor.moduleEntry M a) n ≃ₗ[R]
      (DiagonalHomology.Unmatched (e n) → M) := by
  letI : ∀ i : I n, Subsingleton (M ⧸ LinearMap.range (ScalarBlockTensor.moduleEntry M a n i)) :=
    fun i => quotientSubsingleton M (a n i) (hin i)
  letI : ∀ i : I (n+1), Subsingleton (LinearMap.ker (ScalarBlockTensor.moduleEntry M a (n+1) i)) :=
    fun i => kernelSubsingleton M (a (n+1) i) (hout i)
  exact {
    toFun := fun x => x.1.1
    invFun := fun x => ((x,0),0)
    left_inv := fun x => Prod.ext (Prod.ext rfl (Subsingleton.elim _ _)) (Subsingleton.elim _ _)
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

#print axioms kernelSubsingleton
#print axioms quotientSubsingleton
#print axioms termsEquiv
end Verification.ScalarUnitHomology
