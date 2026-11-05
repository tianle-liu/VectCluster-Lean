/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.TwoTermCoordinateScaling
import Verification.LaurentScalarModel

/-!
# Laurent Mutable Scaling

Mutable rescaling by frozen Laurent monomials on the actual exchange
quotient. The new frozen character is f_i + sum_r P_ri u_r; the partner
is rescaled by the common negative monomial divided by the original unit.
Both coordinate directions remain regular on every mutable zero stratum.
-/
noncomputable section
namespace Verification.LaurentMutableScaling
open MvPolynomial Verification.ExchangeCharacters Verification.LaurentScalarModel
open scoped BigOperators
variable (R : Type*) [CommRing R] {ι M : Type*} [Fintype ι] [AddCommGroup M]
variable (P : ι → ι → ℤ) (f : ι → M) (c : ι → Rˣ) (u : ι → M)

def monomialUnit (v : M) : (Coefficients R M)ˣ :=
  (MonoidAlgebra.of R (Multiplicative M)).toHomUnits (Multiplicative.ofAdd v)

def coefficient (i : ι) : (Coefficients R M)ˣ :=
  Units.map (algebraMap R (Coefficients R M)).toMonoidHom (c i)*monomialUnit R (f i)

def transformed (i : ι) : M := f i+column Finset.univ (fun r=>P r i) u

def common (i : ι) : (Coefficients R M)ˣ := negativeUnit Finset.univ (fun r=>P r i) u

theorem positive_balance (i : ι) :
    coefficient R f c i*∏ r,monomialUnit R (u r)^(P r i).toNat=
      common R P u i*coefficient R (transformed P f u) c i := by
  apply Units.ext
  simp only [coefficient,Units.val_mul,Units.coe_prod,Units.val_pow_eq_pow_val]
  change (algebraMap R (Coefficients R M) (c i : R)*monomial (f i)) *
    (∏ r,monomial (u r)^(P r i).toNat)=monomial (negative Finset.univ (fun r=>P r i) u)*
      (algebraMap R (Coefficients R M) (c i : R)*monomial (transformed P f u i))
  rw [← positive_monomial,positive_eq_negative_add_column,transformed,monomial_add,monomial_add]
  ring

theorem negative_balance (i : ι) :
    (1 : (Coefficients R M)ˣ)*∏ r,monomialUnit R (u r)^(-P r i).toNat=common R P u i*1 := by
  apply Units.ext
  simp only [Units.val_mul,Units.val_one,one_mul,mul_one,Units.coe_prod,Units.val_pow_eq_pow_val]
  change (∏ r,monomial (u r)^(-P r i).toNat)=monomial (negative Finset.univ (fun r=>P r i) u)
  exact (negative_monomial _ _ _).symm

theorem relations_eq : LaurentScalarModel.relations R P f c=
    ScalarExchangeRelabel.relations (Coefficients R M) id P (coefficient R f c) (fun _=>1) := by
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  simp only [PartnerScaling.relation,ScalarExchangeRelabel.relation,ScalarExchangeRelabel.powerSum,
    id_eq,coefficient,Units.val_mul,Units.val_one,map_one,one_mul,LaurentScalarModel.exchange]
  rfl

def presentationEquiv : Presentation R P f c ≃ₐ[R] Presentation R P (transformed P f u) c :=
  ((Ideal.quotientEquivAlgOfEq (Coefficients R M) (relations_eq R P f c)).trans
    ((TwoTermCoordinateScaling.quotientEquiv (Coefficients R M) id P
      (coefficient R f c) (fun _=>1) (coefficient R (transformed P f u) c) (fun _=>1)
      (fun r=>monomialUnit R (u r)) (common R P u) (positive_balance R P f c u) (negative_balance R P u)).trans
      (Ideal.quotientEquivAlgOfEq (Coefficients R M) (relations_eq R P (transformed P f u) c).symm))).restrictScalars R

theorem presentation_original (i : ι) :
    presentationEquiv R P f c u (Ideal.Quotient.mk _ (C (X i)))=
      algebraMap (Coefficients R M) _ (monomial (u i))*
        (Ideal.Quotient.mk _ (C (X i)) : Presentation R P (transformed P f u) c) := by
  change Ideal.Quotient.mk _ (TwoTermCoordinateScaling.ambient (Coefficients R M) id
    (fun r=>monomialUnit R (u r)) (common R P u) (C (X i)))=_
  rw [TwoTermCoordinateScaling.ambient_original,map_mul]
  rfl

theorem presentation_partner (i : ι) :
    presentationEquiv R P f c u (Ideal.Quotient.mk _ (X i))=
      algebraMap (Coefficients R M) _ ((common R P u i/monomialUnit R (u i) : (Coefficients R M)ˣ) : Coefficients R M)*
        (Ideal.Quotient.mk _ (X i) : Presentation R P (transformed P f u) c) := by
  change Ideal.Quotient.mk _ (TwoTermCoordinateScaling.ambient (Coefficients R M) id
    (fun r=>monomialUnit R (u r)) (common R P u) (X i))=_
  rw [TwoTermCoordinateScaling.ambient_X,map_mul]
  rfl

#print axioms monomialUnit
#print axioms coefficient
#print axioms transformed
#print axioms common
#print axioms positive_balance
#print axioms negative_balance
#print axioms relations_eq
#print axioms presentationEquiv
#print axioms presentation_original
#print axioms presentation_partner
end Verification.LaurentMutableScaling
