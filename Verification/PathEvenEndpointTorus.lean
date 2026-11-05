/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathSignedStratumEquivalence
import Verification.IndexedTorusSpecialization

/-!
# Path Even Endpoint Torus

For Y of even length the endpoint classes have opposite parity and are
distinct. Evaluating their exact signed units leaves the actual free Laurent
coordinates; adjoining the selected partners gives the entire path stratum.
-/
noncomputable section
namespace Verification.PathEvenEndpointTorus
open Classical Verification.PathCompression Verification.PathClassRepresentatives
open Verification.PathSignedStratumCoefficients Verification.PathLiteralStratum
open Verification.OriginalTorus Verification.FinsuppTorusUniversal
open Finset MvPolynomial

theorem representative_parity (I : Finset ℕ) (p : ℕ) : representative I p%2=p%2 := by
  induction p using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more p ih _ =>
    rw [representative]
    split_ifs
    · omega
    · rfl

variable {a : ℕ} {I : Finset ℕ} (hI : Admissible (2*a) I)

def endpointClass (e : Bool) : Representatives (2*a) I := compress hI (endpoint hI e)

theorem first_parity : (endpointClass hI false).val%2=0 := rfl

theorem last_parity : (endpointClass hI true).val%2=1 := by
  change representative I (2*a+1)%2=1
  rw [representative_parity]
  omega

theorem endpointClass_injective : Function.Injective (endpointClass hI) := by
  intro e f hef
  cases e <;> cases f
  · rfl
  · have hh := congrArg (fun p : Representatives (2*a) I => p.val%2) hef
    dsimp only at hh
    rw [first_parity,last_parity] at hh
    omega
  · have hh := congrArg (fun p : Representatives (2*a) I => p.val%2) hef
    dsimp only at hh
    rw [last_parity,first_parity] at hh
    omega
  · rfl

variable (R : Type) [CommRing R]

def endpointUnit (e : Bool) : Rˣ := if e then (-1)^a else 1

theorem endpointUnit_value (e : Bool) : (endpointUnit (a:=a) R e : R)=endpointValue R (n:=2*a) 1 1 e := by
  have ha : (2*a+1)/2=a := by omega
  cases e <;> simp [endpointUnit,endpointValue,ha]

theorem endpointIdeal_eq : endpointIdeal R hI 1 1=
    IndexedTorusSpecialization.ideal R (Representatives (2*a) I) Bool (endpointClass hI) (endpointUnit (a:=a) R) := by
  unfold endpointIdeal IndexedTorusSpecialization.ideal
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext e
  rw [endpointUnit_value]
  rfl

abbrev FreeCoordinates := {p : Representatives (2*a) I // p ∉ Set.range (endpointClass hI)}

def coefficientEquiv : Coefficients R hI 1 1 ≃ₐ[R] Torus R (FreeCoordinates hI) :=
  (Ideal.quotientEquivAlgOfEq R (endpointIdeal_eq hI R)).trans
    (IndexedTorusSpecialization.specializationEquiv R (Representatives (2*a) I) Bool
      (endpointClass hI) (endpointClass_injective hI) (endpointUnit (a:=a) R))

theorem coefficient_coordinate (p : FreeCoordinates hI) : coefficientEquiv hI R
    (Ideal.Quotient.mk (endpointIdeal R hI 1 1) (torusCoordinate R _ p.val))=torusCoordinate R _ p := by
  rw [coefficientEquiv,AlgEquiv.trans_apply,Ideal.quotientEquivAlgOfEq_mk]
  exact IndexedTorusSpecialization.specialization_free R (Representatives (2*a) I) Bool
    (endpointClass hI) (endpointClass_injective hI) (endpointUnit (a:=a) R) p

def stratumEquiv : Layer R hI 1 1 ≃ₐ[R] MvPolynomial I (Torus R (FreeCoordinates hI)) :=
  (PathSignedStratumEquivalence.stratumEquiv R hI 1 1).trans (MvPolynomial.mapAlgEquiv I (coefficientEquiv hI R))

theorem stratum_partner (i : I) : stratumEquiv hI R (layerY R hI 1 1 (mutableIndex hI i))=X i := by
  change MvPolynomial.map (coefficientEquiv hI R).toRingHom
    (PathSignedStratumEquivalence.stratumEquiv R hI 1 1 (layerY R hI 1 1 (mutableIndex hI i)))=_
  rw [PathSignedStratumEquivalence.stratumEquiv_partner,MvPolynomial.map_X]

theorem stratum_free_coordinate (p : FreeCoordinates hI) :
    stratumEquiv hI R (signedUnit R hI 1 1 (includeRepresentative p.val) : Layer R hI 1 1)=C (torusCoordinate R _ p) := by
  change MvPolynomial.map (coefficientEquiv hI R).toRingHom
    (PathSignedStratumEquivalence.stratumEquiv R hI 1 1 (signedUnit R hI 1 1 (includeRepresentative p.val) : Layer R hI 1 1))=_
  rw [PathSignedStratumEquivalence.stratumEquiv_signed,MvPolynomial.map_C]
  change C (coefficientEquiv hI R
    (Ideal.Quotient.mk (endpointIdeal R hI 1 1) (torusCoordinate R _ (compress hI (includeRepresentative p.val)))))=_
  rw [compress_include,coefficient_coordinate]

omit [CommRing R] in
theorem rank_formula : Fintype.card (FreeCoordinates hI)+2*I.card=2*a := by
  have hc : Fintype.card (Representatives (2*a) I)=(available I (2*a+2)).card := Fintype.card_coe _
  have he : Fintype.card (Set.range (endpointClass hI))=2 := by
    rw [← Fintype.card_congr (Equiv.ofInjective (endpointClass hI) (endpointClass_injective hI)),Fintype.card_bool]
  have hb := Fintype.card_le_of_injective _ (endpointClass_injective hI)
  rw [Fintype.card_bool] at hb
  have hr := available_card hI
  change Fintype.card {p : Representatives (2*a) I // p ∉ Set.range (endpointClass hI)}+2*I.card=2*a
  rw [Fintype.card_subtype_compl,he]
  omega

#print axioms representative_parity
#print axioms endpointClass
#print axioms first_parity
#print axioms last_parity
#print axioms endpointClass_injective
#print axioms endpointUnit
#print axioms endpointUnit_value
#print axioms endpointIdeal_eq
#print axioms FreeCoordinates
#print axioms coefficientEquiv
#print axioms coefficient_coordinate
#print axioms stratumEquiv
#print axioms stratum_partner
#print axioms stratum_free_coordinate
#print axioms rank_formula
end Verification.PathEvenEndpointTorus
