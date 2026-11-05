/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FreeCharacterQuotientCoordinates

/-!
# Free Character Remaining Coordinates

A coefficient character is preserved through the named-coordinate
quotient splitting, with the free coordinate component equal to zero.
-/
noncomputable section
namespace Verification.FreeCharacterRemainingCoordinates
variable (R M P Q ι : Type) [CommRing R] [AddCommGroup M]
  [AddCommGroup P] [AddCommGroup Q]
variable (e : M ≃ₗ[ℤ] P × Q) (c : ι → M) (u : ι → R)
variable (hc : ∀ i, (e (c i)).1 = 0)
variable (J : Ideal (MonoidAlgebra R (Multiplicative M)))
variable (hJ : J = FreeCharacterFactor.sourceIdeal R M ι c u)

theorem remaining_of_image (m : M) (q : Q) (hm : e m = (0, q)) :
    FreeCharacterQuotientCoordinates.equiv R M P Q ι e c u hc J hJ
      (Ideal.Quotient.mk J (MonoidAlgebra.of R _ (Multiplicative.ofAdd m))) =
      algebraMap
        (MonoidAlgebra R (Multiplicative Q) ⧸ FreeCharacterFactor.coefficientIdeal R M P Q ι e c u)
        (MonoidAlgebra (MonoidAlgebra R (Multiplicative Q) ⧸
          FreeCharacterFactor.coefficientIdeal R M P Q ι e c u) (Multiplicative P))
        (Ideal.Quotient.mk _ (MonoidAlgebra.of R _ (Multiplicative.ofAdd q))) := by
  dsimp only [FreeCharacterQuotientCoordinates.equiv, AlgEquiv.trans_apply]
  rw [Ideal.quotientEquivAlgOfEq_mk, FreeCharacterFactor.equiv_monomial, hm]
  rfl

#print axioms remaining_of_image
end Verification.FreeCharacterRemainingCoordinates
