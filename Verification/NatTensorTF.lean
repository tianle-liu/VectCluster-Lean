/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FiniteFreeTensorTF
import Verification.NatComplexIntegerFree

/-!
# Nat Tensor TF

The TF specialization for natural cochain degrees, using the actual
integral homology at p and p+1 and the constructed unmatched Smith slots.
-/
noncomputable section
namespace Verification.NatTensorTF
open CategoryTheory
attribute [local instance] NatComplexIntegerFree.free NatComplexIntegerFree.finite
variable {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable (C : CochainComplex (ModuleCat.{0} R) ℕ)
variable [∀ p, Module.Free R (C.X p)] [∀ p, Module.Finite R (C.X p)]
variable (M : Type) [AddCommGroup M] [Module R M]

omit [IsDomain R] [IsPrincipalIdealRing R]
  [∀ p, Module.Free R (C.X p)] [∀ p, Module.Finite R (C.X p)] in
theorem extended_tf (p : ℕ) (h : NoZeroSMulDivisors R (C.homology p)) :
    NoZeroSMulDivisors R ((NatComplexIntegerExtension.extended C).homology (p : ℤ)) := by
  letI := h
  let e := (C.extendHomologyIso ComplexShape.embeddingUpNat (j := p) rfl).toLinearEquiv
  exact Function.Injective.noZeroSMulDivisors e e.injective e.map_zero e.map_smul

def homologyEquiv (p : ℕ) (hp : 0 < p) (hin : NoZeroSMulDivisors R (C.homology p))
    (hout : NoZeroSMulDivisors R (C.homology (p+1))) :
    (IntegerTensorExtension.complex R M C).homology p ≃ₗ[R]
      (DiagonalHomology.Unmatched (SmithCoefficientComplex.embedding
        (NatComplexIntegerExtension.extended C) (p : ℤ)) → M) :=
  (NatComplexIntegerExtension.mappedHomologyIso C (IntegerTensorExtension.functor R M) p hp).symm.toLinearEquiv.trans
    (FiniteFreeTensorTF.homologyEquiv (NatComplexIntegerExtension.extended C) M (p : ℤ)
      (extended_tf C p hin) (by simpa only [Nat.cast_add,Nat.cast_one] using extended_tf C (p+1) hout))

#print axioms extended_tf
#print axioms homologyEquiv
end Verification.NatTensorTF
