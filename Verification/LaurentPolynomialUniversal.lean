/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LaurentBasepoint

/-!
# Laurent Polynomial Universal

Universal maps of the literal principal localization of Polynomial.X,
the same Laurent presentation used by the actual purity boundary.
-/
noncomputable section
namespace Verification.LaurentPolynomialUniversal
variable {R S T : Type} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]

abbrev Laurent (S : Type) [CommRing S] := LaurentBasepoint.Laurent S

def parameter (S : Type) [CommRing S] : Laurent S :=
  algebraMap (Polynomial S) (Laurent S) Polynomial.X

def parameterUnit (S : Type) [CommRing S] : (Laurent S)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (Polynomial.X : Polynomial S)).unit

theorem parameterUnit_val : (parameterUnit S : Laurent S)=parameter S :=
  (IsLocalization.Away.algebraMap_isUnit (Polynomial.X : Polynomial S)).unit_spec

def polynomialMap (f : S →ₐ[R] T) (u : Tˣ) : Polynomial S →ₐ[R] T :=
  Polynomial.aevalTower f (u:T)

theorem polynomial_units (f : S →ₐ[R] T) (u : Tˣ)
    (m : Submonoid.powers (Polynomial.X : Polynomial S)) :
    IsUnit (polynomialMap f u m) := by
  obtain ⟨n,hn⟩ := m.2
  rw [← hn,map_pow]
  change IsUnit ((Polynomial.aevalTower _ _ Polynomial.X)^n)
  rw [Polynomial.aevalTower_X]
  exact u.isUnit.pow n

def lift (f : S →ₐ[R] T) (u : Tˣ) : Laurent S →ₐ[R] T :=
  IsLocalization.liftAlgHom (polynomial_units f u)

theorem lift_polynomial (f : S →ₐ[R] T) (u : Tˣ) (p : Polynomial S) :
    lift f u (algebraMap (Polynomial S) (Laurent S) p)=polynomialMap f u p :=
  IsLocalization.lift_eq _ _

theorem lift_parameter (f : S →ₐ[R] T) (u : Tˣ) : lift f u (parameter S)=(u:T) := by
  rw [parameter,lift_polynomial]
  exact Polynomial.aevalTower_X _ _

theorem lift_coefficient (f : S →ₐ[R] T) (u : Tˣ) (s : S) :
    lift f u (algebraMap S (Laurent S) s)=f s := by
  rw [IsScalarTower.algebraMap_apply S (Polynomial S) (Laurent S),lift_polynomial]
  exact Polynomial.aevalTower_C _ _ _

theorem hom_ext (f g : Laurent S →ₐ[R] T)
    (hc : ∀ s, f (algebraMap S (Laurent S) s)=g (algebraMap S (Laurent S) s))
    (hp : f (parameter S)=g (parameter S)) : f=g := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial S))
  apply Polynomial.ringHom_ext
  · exact hc
  · exact hp

#print axioms Laurent
#print axioms parameter
#print axioms parameterUnit
#print axioms parameterUnit_val
#print axioms polynomialMap
#print axioms polynomial_units
#print axioms lift
#print axioms lift_polynomial
#print axioms lift_parameter
#print axioms lift_coefficient
#print axioms hom_ext
end Verification.LaurentPolynomialUniversal
