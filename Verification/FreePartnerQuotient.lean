/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PolynomialQuotient

/-!
# Free Partner Quotient

Separate a genuinely unconstrained exchange partner from an actual
polynomial quotient. This is the affine factor needed for a freezing divisor.
-/
noncomputable section
namespace Verification.FreePartnerQuotient
open MvPolynomial
variable {R S α ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
attribute [local instance] MvPolynomial.algebraMvPolynomial

def coefficientEquiv (J : Ideal S) :
    (MvPolynomial α S ⧸ J.map (C : S →+* MvPolynomial α S)) ≃ₐ[R]
      MvPolynomial α (S ⧸ J) :=
  AlgEquiv.ofRingEquiv (f := PolynomialQuotient.coefficientQuotientEquiv J) (fun r => by
    change PolynomialQuotient.coefficientQuotientEquiv J
      (Ideal.Quotient.mk _ (C (algebraMap R S r))) =
        C (Ideal.Quotient.mk J (algebraMap R S r))
    rw [PolynomialQuotient.coefficientQuotientEquiv_mk, map_C])

def relations (J : Ideal (MvPolynomial ι R)) : Ideal (MvPolynomial (α ⊕ ι) R) :=
  J.map (rename (Sum.inr : ι → α ⊕ ι)).toRingHom

theorem map_relations (J : Ideal (MvPolynomial ι R)) :
    (relations (α := α) J).map (sumAlgEquiv R α ι).toRingHom =
      J.map (C : MvPolynomial ι R →+* MvPolynomial α (MvPolynomial ι R)) := by
  rw [relations, Ideal.map_map]
  apply congrArg (Ideal.map · J)
  exact congrArg AlgHom.toRingHom (sumAlgEquiv_comp_rename_inr R α ι)

def quotientEquiv (J : Ideal (MvPolynomial ι R)) :
    (MvPolynomial (α ⊕ ι) R ⧸ relations (α := α) J) ≃ₐ[R]
      MvPolynomial α (MvPolynomial ι R ⧸ J) :=
  (Ideal.quotientEquivAlg _ _ (sumAlgEquiv R α ι) (map_relations J).symm).trans
    (coefficientEquiv (R := R) J)

theorem quotientEquiv_free (J : Ideal (MvPolynomial ι R)) (a : α) :
    quotientEquiv J (Ideal.Quotient.mk (relations J) (X (Sum.inl a))) = X a := by
  dsimp only [quotientEquiv, AlgEquiv.trans_apply, coefficientEquiv, AlgEquiv.ofRingEquiv_apply]
  change MvPolynomial.map (Ideal.Quotient.mk J)
    (sumAlgEquiv R α ι (X (Sum.inl a))) = X a
  simp

theorem quotientEquiv_retained (J : Ideal (MvPolynomial ι R)) (i : ι) :
    quotientEquiv (α := α) J (Ideal.Quotient.mk (relations J) (X (Sum.inr i))) =
      C (Ideal.Quotient.mk J (X i)) := by
  dsimp only [quotientEquiv, AlgEquiv.trans_apply, coefficientEquiv, AlgEquiv.ofRingEquiv_apply]
  change MvPolynomial.map (Ideal.Quotient.mk J)
    (sumAlgEquiv R α ι (X (Sum.inr i))) = C (Ideal.Quotient.mk J (X i))
  simp

#print axioms coefficientEquiv
#print axioms relations
#print axioms map_relations
#print axioms quotientEquiv
#print axioms quotientEquiv_free
#print axioms quotientEquiv_retained
end Verification.FreePartnerQuotient
