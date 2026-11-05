/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LaurentUnitCoordinates
import Mathlib.RingTheory.MvPolynomial.MonomialOrder

/-!
# Integral Polynomial Units

Affine factors contribute no new units over a domain. The proof uses
the degrees of a polynomial unit and its inverse, so the removal of affine
coordinates in the unit calculation is an internal theorem.
-/
noncomputable section
namespace Verification.IntegralPolynomialUnits
open MvPolynomial
variable (R ι : Type) [CommRing R] [IsDomain R] [Fintype ι]

theorem unit_constant (u : (MvPolynomial ι R)ˣ) :
    (u : MvPolynomial ι R)=C (constantCoeff (u : MvPolynomial ι R)) := by
  classical
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  let m : MonomialOrder ι := MonomialOrder.lex
  have h := m.degree_mul u.ne_zero (u⁻¹).ne_zero
  have he : (u : MvPolynomial ι R)*(u⁻¹ : (MvPolynomial ι R)ˣ)=1 := u.val_inv
  rw [he,m.degree_one] at h
  have hc := m.eq_C_of_degree_eq_zero (add_eq_zero.mp h.symm).1
  have hh : constantCoeff (u : MvPolynomial ι R)=m.leadingCoeff (u : MvPolynomial ι R) := by
    simpa only [constantCoeff_C] using congrArg (constantCoeff : MvPolynomial ι R→R) hc
  rw [hh]
  exact hc

def constants : Rˣ →* (MvPolynomial ι R)ˣ := Units.map (C : R→+*MvPolynomial ι R).toMonoidHom

def evaluate : (MvPolynomial ι R)ˣ →* Rˣ := Units.map (constantCoeff : MvPolynomial ι R→+*R).toMonoidHom

omit [IsDomain R] [Fintype ι] in
theorem evaluate_constants (u : Rˣ) : evaluate R ι (constants R ι u)=u := by
  apply Units.ext
  change constantCoeff (C (u:R) : MvPolynomial ι R)=(u:R)
  simp

theorem constants_evaluate (u : (MvPolynomial ι R)ˣ) : constants R ι (evaluate R ι u)=u :=
  Units.ext (unit_constant R ι u).symm

def unitEquiv : Rˣ ≃* (MvPolynomial ι R)ˣ :=
  { constants R ι with
    invFun := evaluate R ι
    left_inv := evaluate_constants R ι
    right_inv := constants_evaluate R ι }

#print axioms unit_constant
#print axioms constants
#print axioms evaluate
#print axioms evaluate_constants
#print axioms constants_evaluate
#print axioms unitEquiv
end Verification.IntegralPolynomialUnits
