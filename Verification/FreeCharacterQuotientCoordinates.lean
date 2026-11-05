/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FreeCharacterFactor

/-!
# Free Character Quotient Coordinates

Preserve free characters through an equality of presentation ideals.
Keeping this calculation generic also avoids reducing the concrete
exchange-matrix presentation inside the kernel's conversion checker.
-/
noncomputable section
namespace Verification.FreeCharacterQuotientCoordinates
variable (R M P Q ι : Type) [CommRing R] [AddCommGroup M]
  [AddCommGroup P] [AddCommGroup Q]
variable (e : M ≃ₗ[ℤ] P×Q) (c : ι→M) (u : ι→R)
variable (hc : ∀ i,(e (c i)).1=0)
variable (J : Ideal (MonoidAlgebra R (Multiplicative M)))
variable (hJ : J=FreeCharacterFactor.sourceIdeal R M ι c u)

def equiv := (Ideal.quotientEquivAlgOfEq R hJ).trans
  (FreeCharacterFactor.equiv R M P Q ι e c u hc)

theorem free_of_image (m : M) (p : P) (hm : e m=(p,0)) :
    equiv R M P Q ι e c u hc J hJ
      (Ideal.Quotient.mk J (MonoidAlgebra.of R (Multiplicative M) (Multiplicative.ofAdd m))) =
      MonoidAlgebra.of
        (MonoidAlgebra R (Multiplicative Q) ⧸ FreeCharacterFactor.coefficientIdeal R M P Q ι e c u)
        (Multiplicative P) (Multiplicative.ofAdd p) := by
  have h : m=e.symm (p,0) := by rw [← hm,LinearEquiv.symm_apply_apply]
  rw [h]
  simp only [equiv,AlgEquiv.trans_apply,Ideal.quotientEquivAlgOfEq_mk]
  exact FreeCharacterFactor.equiv_free R M P Q ι e c u hc p

#print axioms equiv
#print axioms free_of_image
end Verification.FreeCharacterQuotientCoordinates
