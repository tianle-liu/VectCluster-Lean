/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SplitExchangeChart

/-!
# Single Laurent

Universal maps and the sign involution of the actual localization
R[t,t^{-1}], with compatibility over an arbitrary smaller base ring.
-/
noncomputable section
namespace Verification.SingleLaurent
open MvPolynomial
variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]
attribute [local instance] MvPolynomial.algebraMvPolynomial

abbrev Laurent (S : Type*) [CommRing S] := Verification.SplitExchangeChart.Laurent S PUnit

def parameter (S : Type*) [CommRing S] : Laurent S :=
  Verification.SplitExchangeChart.laurentVariable S PUnit PUnit.unit

def parameterUnit (S : Type*) [CommRing S] : (Laurent S)ˣ :=
  (Verification.SplitExchangeChart.laurentVariable_unit S PUnit PUnit.unit).unit

theorem parameterUnit_val : (parameterUnit S : Laurent S) = parameter S :=
  (Verification.SplitExchangeChart.laurentVariable_unit S PUnit PUnit.unit).unit_spec

def polynomialMap (f : S →ₐ[R] T) (u : Tˣ) : MvPolynomial PUnit S →ₐ[R] T :=
  aevalTower f (fun _ => (u:T))

theorem polynomialMap_units (f : S →ₐ[R] T) (u : Tˣ)
    (m : Verification.SplitExchangeChart.variableMonoid S PUnit) : IsUnit (polynomialMap f u m) := by
  apply Verification.SplitExchangeChart.units_on_closure (polynomialMap f u).toRingHom X _ m
  intro i
  change IsUnit (aevalTower f (fun _ : PUnit => (u:T)) (X i))
  rw [aevalTower_X]
  exact u.isUnit

def lift (f : S →ₐ[R] T) (u : Tˣ) : Laurent S →ₐ[R] T :=
  IsLocalization.liftAlgHom (polynomialMap_units f u)

@[simp] theorem lift_parameter (f : S →ₐ[R] T) (u : Tˣ) : lift f u (parameter S) = (u:T) := by
  change IsLocalization.lift (polynomialMap_units f u)
    (algebraMap (MvPolynomial PUnit S) _ (X PUnit.unit)) = _
  rw [IsLocalization.lift_eq]
  exact aevalTower_X _ _ _

@[simp] theorem lift_coefficient (f : S →ₐ[R] T) (u : Tˣ) (s : S) :
    lift f u (algebraMap S (Laurent S) s) = f s := by
  rw [IsScalarTower.algebraMap_apply S (MvPolynomial PUnit S) (Laurent S)]
  change IsLocalization.lift (polynomialMap_units f u)
    (algebraMap (MvPolynomial PUnit S) _ (C s)) = _
  rw [IsLocalization.lift_eq]
  exact aevalTower_C _ _ _

theorem hom_ext (f g : Laurent S →ₐ[R] T)
    (hc : ∀ s, f (algebraMap S (Laurent S) s) = g (algebraMap S (Laurent S) s))
    (hp : f (parameter S) = g (parameter S)) : f = g := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Verification.SplitExchangeChart.variableMonoid S PUnit)
  apply MvPolynomial.ringHom_ext
  · exact hc
  · intro i
    cases i
    exact hp

def signHom (R : Type*) [CommRing R] : Laurent R →ₐ[R] Laurent R :=
  lift (Algebra.ofId R (Laurent R)) (-parameterUnit R)

@[simp] theorem signHom_parameter : signHom R (parameter R) = -parameter R := by
  rw [signHom, lift_parameter, Units.val_neg, parameterUnit_val]

theorem signHom_squared : (signHom R).comp (signHom R) = AlgHom.id R _ := by
  apply hom_ext
  · intro r
    simp only [AlgHom.comp_apply, AlgHom.commutes, AlgHom.id_apply]
  · simp only [AlgHom.comp_apply, signHom_parameter, map_neg, neg_neg, AlgHom.id_apply]

def signEquiv (R : Type*) [CommRing R] : Laurent R ≃ₐ[R] Laurent R :=
  AlgEquiv.ofAlgHom (signHom R) (signHom R) signHom_squared signHom_squared

@[simp] theorem signEquiv_parameter : signEquiv R (parameter R) = -parameter R :=
  signHom_parameter

#print axioms Laurent
#print axioms parameter
#print axioms parameterUnit
#print axioms parameterUnit_val
#print axioms polynomialMap
#print axioms polynomialMap_units
#print axioms lift
#print axioms lift_parameter
#print axioms lift_coefficient
#print axioms hom_ext
#print axioms signHom
#print axioms signHom_parameter
#print axioms signHom_squared
#print axioms signEquiv
#print axioms signEquiv_parameter
end Verification.SingleLaurent
