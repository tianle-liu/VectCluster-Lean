/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PolynomialQuotient

/-!
# Polynomial Coefficient Algebra

Algebra versions of imposing coefficient constraints in a polynomial
presentation, including arbitrary further polynomial equations.
-/
noncomputable section
namespace Verification.PolynomialCoefficientAlgebra
open MvPolynomial Verification.PolynomialQuotient
variable {S α : Type*} [CommRing S]
attribute [local instance] MvPolynomial.algebraMvPolynomial

def coefficientEquiv (J : Ideal S) :
    CoefficientQuotient (α := α) J ≃ₐ[S] MvPolynomial α (S ⧸ J) :=
  AlgEquiv.ofRingEquiv (f := coefficientQuotientEquiv J) (fun s => by
    change MvPolynomial.map (Ideal.Quotient.mk J) (C s) = C (Ideal.Quotient.mk J s)
    rw [map_C])

theorem coefficientEquiv_mk (J : Ideal S) (p : MvPolynomial α S) :
    coefficientEquiv J (Ideal.Quotient.mk (coefficientIdeal J) p) =
      MvPolynomial.map (Ideal.Quotient.mk J) p := rfl

def combinedEquiv (J : Ideal S) (K : Ideal (MvPolynomial α S)) :
    (MvPolynomial α S ⧸ (coefficientIdeal J ⊔ K)) ≃ₐ[S]
      (MvPolynomial α (S ⧸ J) ⧸ K.map (MvPolynomial.map (Ideal.Quotient.mk J))) :=
  (DoubleQuot.quotQuotEquivQuotSupₐ S (coefficientIdeal J) K).symm.trans
    (Ideal.quotientEquivAlg _ _ (coefficientEquiv J) (transport_ideal J K).symm)

theorem combinedEquiv_mk (J : Ideal S) (K : Ideal (MvPolynomial α S))
    (p : MvPolynomial α S) :
    combinedEquiv J K (Ideal.Quotient.mk (coefficientIdeal J ⊔ K) p) =
      Ideal.Quotient.mk (K.map (MvPolynomial.map (Ideal.Quotient.mk J)))
        (MvPolynomial.map (Ideal.Quotient.mk J) p) := by
  change Ideal.quotientEquivAlg _ _ (coefficientEquiv J) (transport_ideal J K).symm
    ((DoubleQuot.quotQuotEquivQuotSup (coefficientIdeal J) K).symm
      (Ideal.Quotient.mk (coefficientIdeal J ⊔ K) p)) = _
  rw [DoubleQuot.quotQuotEquivQuotSup_symm_quotQuotMk]
  rfl

#print axioms coefficientEquiv
#print axioms coefficientEquiv_mk
#print axioms combinedEquiv
#print axioms combinedEquiv_mk
end Verification.PolynomialCoefficientAlgebra
