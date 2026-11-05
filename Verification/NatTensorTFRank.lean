/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.NatTensorTF
import Verification.TensorUnitComplex
import Mathlib.Data.Fintype.EquivFin

/-!
# Nat Tensor TF Rank

The surviving Smith slots are counted by the rank of the actual
integral cohomology, so the TF coefficient result is a power with exactly
that exponent rather than an unrelated free-module cardinal.
-/
noncomputable section
open scoped Classical
namespace Verification.NatTensorTFRank
open CategoryTheory
attribute [local instance] NatComplexIntegerFree.free NatComplexIntegerFree.finite
variable {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable (C : CochainComplex (ModuleCat.{0} R) ℕ)
variable [∀ p, Module.Free R (C.X p)] [∀ p, Module.Finite R (C.X p)]
variable (p : ℕ) (hp : 0 < p) (hin : NoZeroSMulDivisors R (C.homology p))
variable (hout : NoZeroSMulDivisors R (C.homology (p+1)))

def integralEquiv : C.homology p ≃ₗ[R]
    (DiagonalHomology.Unmatched (SmithCoefficientComplex.embedding
      (NatComplexIntegerExtension.extended C) (p : ℤ)) → R) :=
  (TensorUnitComplex.homologyIso R C p).symm.toLinearEquiv.trans
    (NatTensorTF.homologyEquiv C R p hp hin hout)

include hp hin hout in
theorem surviving_card :
    Fintype.card (DiagonalHomology.Unmatched (SmithCoefficientComplex.embedding
      (NatComplexIntegerExtension.extended C) (p : ℤ))) = Module.finrank R (C.homology p) := by
  have h := (integralEquiv C p hp hin hout).finrank_eq
  simpa only [Module.finrank_pi,Module.finrank_self,mul_one] using h.symm

def coefficientEquiv (M : Type) [AddCommGroup M] [Module R M] :
    (IntegerTensorExtension.complex R M C).homology p ≃ₗ[R]
      (Fin (Module.finrank R (C.homology p)) → M) :=
  (NatTensorTF.homologyEquiv C M p hp hin hout).trans
    (LinearEquiv.piCongrLeft' R (fun _ => M)
      ((Fintype.equivFin _).trans (finCongr (surviving_card C p hp hin hout))))

#print axioms integralEquiv
#print axioms surviving_card
#print axioms coefficientEquiv
end Verification.NatTensorTFRank
