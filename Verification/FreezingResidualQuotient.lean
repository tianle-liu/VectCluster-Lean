/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FreezingPresentation
import Verification.PolynomialCoefficientAlgebra

/-!
# Freezing Residual Quotient

The residual freezing presentation can impose its coefficient
constraints first, while retaining every remaining exchange equation.
-/
noncomputable section
namespace Verification.FreezingResidualQuotient
open MvPolynomial Verification.FreezingPresentation
variable {S α ι κ : Type*} [CommRing S]
variable (x g : ((α ⊕ ι) ⊕ κ) → S)
attribute [local instance] MvPolynomial.algebraMvPolynomial

def coefficientIdeal : Ideal S :=
  Ideal.span (Set.range (fun a : α => g (Sum.inl (Sum.inl a))))

theorem coefficientConstraints_eq : coefficientConstraints (ι := ι) g =
    Verification.PolynomialQuotient.coefficientIdeal (coefficientIdeal g) := by
  rw [Verification.PolynomialQuotient.coefficientIdeal, coefficientIdeal,
    Ideal.map_span, ← Set.range_comp]
  rfl

def reducedRelation (i : ι) : MvPolynomial ι (S ⧸ coefficientIdeal g) :=
  C (Ideal.Quotient.mk (coefficientIdeal g) (x (Sum.inl (Sum.inr i)))) * X i -
    C (Ideal.Quotient.mk (coefficientIdeal g) (g (Sum.inl (Sum.inr i))))

theorem map_retainedIdeal :
    (Ideal.span (Set.range (retainedRelation x g))).map
      (MvPolynomial.map (Ideal.Quotient.mk (coefficientIdeal g))) =
      Ideal.span (Set.range (reducedRelation x g)) := by
  rw [Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  simp only [Function.comp_apply, retainedRelation, reducedRelation, map_sub, map_mul,
    map_C, map_X]

def residualEquiv : (MvPolynomial ι S ⧸ remainingIdeal x g) ≃ₐ[S]
    (MvPolynomial ι (S ⧸ coefficientIdeal g) ⧸ Ideal.span (Set.range (reducedRelation x g))) :=
  (Ideal.quotientEquivAlgOfEq S (by
    rw [remainingIdeal, coefficientConstraints_eq (ι := ι) g])).trans
      ((Verification.PolynomialCoefficientAlgebra.combinedEquiv (coefficientIdeal g)
        (Ideal.span (Set.range (retainedRelation x g)))).trans
          (Ideal.quotientEquivAlgOfEq S (map_retainedIdeal x g)))

theorem residualEquiv_mk (p : MvPolynomial ι S) :
    residualEquiv x g (Ideal.Quotient.mk (remainingIdeal x g) p) =
      Ideal.Quotient.mk (Ideal.span (Set.range (reducedRelation x g)))
        (MvPolynomial.map (Ideal.Quotient.mk (coefficientIdeal g)) p) := by
  dsimp only [residualEquiv, AlgEquiv.trans_apply]
  rw [Ideal.quotientEquivAlgOfEq_mk,
    Verification.PolynomialCoefficientAlgebra.combinedEquiv_mk,
    Ideal.quotientEquivAlgOfEq_mk]

#print axioms coefficientIdeal
#print axioms coefficientConstraints_eq
#print axioms reducedRelation
#print axioms map_retainedIdeal
#print axioms residualEquiv
#print axioms residualEquiv_mk
end Verification.FreezingResidualQuotient
