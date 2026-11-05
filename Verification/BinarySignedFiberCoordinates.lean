/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.BinarySignedFiber

/-!
# Binary Signed Fiber Coordinates

Explicit monomial formula for the signed binary quotient.
-/
noncomputable section
namespace Verification.BinarySignedFiberCoordinates
open MonoidAlgebra Verification.BinarySignedFiber Verification.SplitTorusFiber
variable {ι M Q : Type*} [Fintype ι] [AddCommGroup M] [Module (ZMod 2) M]
  [AddCommGroup Q] [Module (ZMod 2) Q]

theorem monomial (f : (ι → ZMod 2) →ₗ[ZMod 2] M) (u : ι → ℤˣ)
    (e : M ≃ₗ[ZMod 2] ((ι → ZMod 2) × Q)) (he : ∀ x, e (f x) = (x,0)) (m : M) :
    BinarySignedFiber.fiberEquiv f u e he
      (Ideal.Quotient.mk (prescribedIdeal f u) (of ℤ _ (Multiplicative.ofAdd m))) =
      algebraMap ℤ _ (character u (Multiplicative.ofAdd (e m).1) : ℤ) *
        of ℤ (Multiplicative Q) (Multiplicative.ofAdd (e m).2) := by
  change specialize (character u) (domCongr ℤ ℤ (groupSplitting e)
    (of ℤ _ (Multiplicative.ofAdd m))) = _
  have hh : domCongr ℤ ℤ (groupSplitting e) (of ℤ _ (Multiplicative.ofAdd m)) =
      of ℤ (Multiplicative (ι → ZMod 2) × Multiplicative Q)
        (Multiplicative.ofAdd (e m).1,Multiplicative.ofAdd (e m).2) := by
    change domCongr ℤ ℤ (groupSplitting e) (Finsupp.single _ 1) = Finsupp.single _ 1
    rw [domCongr_single]
    rfl
  rw [hh,specialize_monomial]

def quotientEquiv (f : (ι → ZMod 2) →ₗ[ZMod 2] M) (u : ι → ℤˣ)
    (e : M ≃ₗ[ZMod 2] ((ι → ZMod 2) × Q)) (he : ∀ x, e (f x) = (x,0))
    (J : Ideal (MonoidAlgebra ℤ (Multiplicative M))) (hJ : J = prescribedIdeal f u) :
    (MonoidAlgebra ℤ (Multiplicative M) ⧸ J) ≃ₐ[ℤ] MonoidAlgebra ℤ (Multiplicative Q) :=
  (Ideal.quotientEquivAlgOfEq ℤ hJ).trans (BinarySignedFiber.fiberEquiv f u e he)

theorem quotientEquiv_monomial (f : (ι → ZMod 2) →ₗ[ZMod 2] M) (u : ι → ℤˣ)
    (e : M ≃ₗ[ZMod 2] ((ι → ZMod 2) × Q)) (he : ∀ x, e (f x) = (x,0))
    (J : Ideal (MonoidAlgebra ℤ (Multiplicative M))) (hJ : J = prescribedIdeal f u) (m : M) :
    quotientEquiv f u e he J hJ (Ideal.Quotient.mk J (of ℤ _ (Multiplicative.ofAdd m))) =
      algebraMap ℤ _ (character u (Multiplicative.ofAdd (e m).1) : ℤ) *
        of ℤ (Multiplicative Q) (Multiplicative.ofAdd (e m).2) := by
  dsimp only [quotientEquiv,AlgEquiv.trans_apply]
  rw [Ideal.quotientEquivAlgOfEq_mk]
  exact monomial _ _ _ _ _

#print axioms quotientEquiv
#print axioms quotientEquiv_monomial

#print axioms monomial
end Verification.BinarySignedFiberCoordinates
