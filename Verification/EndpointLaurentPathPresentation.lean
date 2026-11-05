/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LaurentExchangeUniversal
import Verification.PathMatrixPresentation

/-!
# Endpoint Laurent Path Presentation

A Laurent character occurring only in the first frozen column is exactly
the endpoint parameter of the literal nearest-neighbour PathAlgebra.
-/
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 600000
namespace Verification.EndpointLaurentPathPresentation
open Classical MvPolynomial
variable (R : Type*) [CommRing R] {M : Type*} [AddCommGroup M]
variable (n : ℕ) (a : M)
abbrev Coeff := LaurentScalarModel.Coefficients R M

def unit : (Coeff R (M:=M))ˣ :=
  (MonoidAlgebra.of R (Multiplicative M)).toHomUnits (Multiplicative.ofAdd a)

theorem unit_val : (unit R a : Coeff R (M:=M))=ExchangeCharacters.monomial a := rfl

def exponent (i : Fin n) : M := if i.val=0 then a else 0

theorem exchange (i : Fin n) :
    LaurentScalarModel.exchange R (PathLattice.pathMatrix n) (exponent n a) (fun _=>1) i=
    ScalarExchangeRelabel.powerSum (Coeff R (M:=M)) (fun r=>PathLattice.pathMatrix n r i)
      (PathMatrixPresentation.leftCoefficient (Coeff R (M:=M)) n (unit R a) i)
      (PathMatrixPresentation.rightCoefficient (Coeff R (M:=M)) n 1 i) := by
  simp only [LaurentScalarModel.exchange,ScalarExchangeRelabel.powerSum,
    Units.val_one,map_one,one_mul,PathMatrixPresentation.rightCoefficient,ite_self]
  by_cases hi : i.val=0
  · simp only [exponent,PathMatrixPresentation.leftCoefficient,if_pos hi,unit_val]
  · simp only [exponent,PathMatrixPresentation.leftCoefficient,if_neg hi,
      ExchangeCharacters.monomial_zero,Units.val_one,map_one,one_mul]

theorem relations :
    LaurentScalarModel.relations R (PathLattice.pathMatrix n) (exponent n a) (fun _=>1)=
    PathMatrixPresentation.matrixRelations (Coeff R (M:=M)) n (unit R a) 1 := by
  unfold LaurentScalarModel.relations PartnerScaling.relations PathMatrixPresentation.matrixRelations
    ScalarExchangeRelabel.relations
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  change C (X i)*X i-C (LaurentScalarModel.exchange R (PathLattice.pathMatrix n) (exponent n a) (fun _=>1) i)=_
  rw [exchange]
  rfl

def equivOverCoefficient :
    LaurentScalarModel.Presentation R (PathLattice.pathMatrix n) (exponent n a) (fun _=>1) ≃ₐ[Coeff R (M:=M)]
      PathPresentation.PathAlgebra n (ExchangeCharacters.monomial (R:=R) a) 1 :=
  (Ideal.quotientEquivAlgOfEq (Coeff R (M:=M)) (relations R n a)).trans
    (PathMatrixPresentation.presentationEquiv (Coeff R (M:=M)) n (unit R a) 1).symm

def equiv :
    LaurentScalarModel.Presentation R (PathLattice.pathMatrix n) (exponent n a) (fun _=>1) ≃ₐ[R]
      PathPresentation.PathAlgebra n (ExchangeCharacters.monomial (R:=R) a) 1 :=
  (equivOverCoefficient R n a).restrictScalars R

#print axioms Coeff
#print axioms unit
#print axioms unit_val
#print axioms exponent
#print axioms exchange
#print axioms relations
#print axioms equivOverCoefficient
#print axioms equiv
end Verification.EndpointLaurentPathPresentation
