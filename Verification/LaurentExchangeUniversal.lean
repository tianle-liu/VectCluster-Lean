/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LaurentScalarModel
import Verification.NestedExchangeUniversal

/-!
# Laurent Exchange Universal

Coordinates and the universal property of the actual Laurent exchange
quotient. The generic nested-quotient theorem is instantiated on its literal
exchange polynomial, keeping every coefficient and mutable coordinate.
-/
noncomputable section
namespace Verification.LaurentExchangeUniversal
open MvPolynomial Verification.LaurentScalarModel
open scoped BigOperators
variable (R : Type*) [CommRing R] {ι M : Type*} [Fintype ι] [AddCommGroup M]
variable (P : ι → ι → ℤ) (f : ι → M) (c : ι → Rˣ)
local instance ambientCommRing : CommRing (MvPolynomial ι (MvPolynomial ι (Coefficients R M))) :=
  LaurentScalarModel.ambientCommRing R ι M

def original (i : ι) : Presentation R P f c :=
  NestedExchangeUniversal.x (Coefficients R M) (exchange R P f c) i
def partner (i : ι) : Presentation R P f c :=
  NestedExchangeUniversal.y (Coefficients R M) (exchange R P f c) i

def value (q : MvPolynomial ι (Coefficients R M)) : Presentation R P f c :=
  NestedExchangeUniversal.value (Coefficients R M) (exchange R P f c) q

theorem equation (i : ι) : original R P f c i*partner R P f c i=
    value R P f c (exchange R P f c i) :=
  NestedExchangeUniversal.equation (Coefficients R M) (exchange R P f c) i

variable {T : Type*} [CommRing T] [Algebra R T]
def expression (φ : Coefficients R M →ₐ[R] T) (x : ι → T) (i : ι) : T :=
  φ (algebraMap R _ (c i : R)*ExchangeCharacters.monomial (f i))*(∏ r,x r^(P r i).toNat)+
    ∏ r,x r^(-P r i).toNat

theorem evaluate_exchange (φ : Coefficients R M →ₐ[R] T) (x : ι → T) (i : ι) :
    aevalTower φ x (exchange R P f c i)=expression R P f c φ x i := by
  simp only [exchange,expression,map_add,map_mul,map_prod,map_pow,aevalTower_C,aevalTower_X]

def lift (φ : Coefficients R M →ₐ[R] T) (x y : ι → T)
    (h : ∀ i,x i*y i=expression R P f c φ x i) : Presentation R P f c →ₐ[R] T :=
  NestedExchangeUniversal.lift R (Coefficients R M) (exchange R P f c) φ x y
    (fun i=>(h i).trans (evaluate_exchange R P f c φ x i).symm)

theorem lift_original (φ : Coefficients R M →ₐ[R] T) (x y : ι → T)
    (h : ∀ i,x i*y i=expression R P f c φ x i) (i : ι) :
    lift R P f c φ x y h (original R P f c i)=x i :=
  NestedExchangeUniversal.lift_x R (Coefficients R M) (exchange R P f c) φ x y _ i

theorem lift_partner (φ : Coefficients R M →ₐ[R] T) (x y : ι → T)
    (h : ∀ i,x i*y i=expression R P f c φ x i) (i : ι) :
    lift R P f c φ x y h (partner R P f c i)=y i :=
  NestedExchangeUniversal.lift_y R (Coefficients R M) (exchange R P f c) φ x y _ i

theorem lift_coefficient (φ : Coefficients R M →ₐ[R] T) (x y : ι → T)
    (h : ∀ i,x i*y i=expression R P f c φ x i) (v : Coefficients R M) :
    lift R P f c φ x y h (algebraMap (Coefficients R M) (Presentation R P f c) v)=φ v :=
  NestedExchangeUniversal.lift_coefficient R (Coefficients R M) (exchange R P f c) φ x y _ v

theorem hom_ext (a b : Presentation R P f c →ₐ[R] T)
    (hc : ∀ v,a (algebraMap (Coefficients R M) _ v)=b (algebraMap (Coefficients R M) _ v))
    (hx : ∀ i,a (original R P f c i)=b (original R P f c i))
    (hy : ∀ i,a (partner R P f c i)=b (partner R P f c i)) : a=b :=
  NestedExchangeUniversal.hom_ext R (Coefficients R M) (exchange R P f c) a b hc hx hy

#print axioms ambientCommRing
#print axioms original
#print axioms partner
#print axioms value
#print axioms equation
#print axioms expression
#print axioms evaluate_exchange
#print axioms lift
#print axioms lift_original
#print axioms lift_partner
#print axioms lift_coefficient
#print axioms hom_ext
end Verification.LaurentExchangeUniversal
