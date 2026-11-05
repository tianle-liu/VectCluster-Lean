/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathSignedStratumCoefficients
import Verification.FinsuppTorusTower
import Verification.LaurentPolynomialUniversal

/-!
# Path Variable Endpoint Maps

Canonical maps for the variable-left-endpoint path. The frozen parameter
is the left surviving coordinate; the right surviving coordinate is evaluated
at its signed constant. This also covers coincident endpoint classes.
-/
noncomputable section
namespace Verification.PathVariableEndpointMaps
open Classical Verification.PathCompression Verification.PathClassRepresentatives
open Verification.PathSignedStratumCoefficients
open Verification.OriginalTorus Verification.FinsuppTorusUniversal
open Verification.LaurentPolynomialUniversal
variable (R : Type) [CommRing R] {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)

def leftClass : Representatives n I := compress hI (firstVertex hI)
def rightClass : Representatives n I := compress hI (lastVertex hI)
abbrev FreeCoordinates := {p : Representatives n I // p ≠ rightClass hI}
abbrev Target := Torus R (FreeCoordinates hI)
abbrev Source := Coefficients (Laurent R) hI (parameter R) 1

def targetUnit (p : Representatives n I) : (Target R hI)ˣ :=
  if hp : p=rightClass hI then (-1)^((n+1)/2) else unit R _ ⟨p,hp⟩

def frozenMap : Laurent R →ₐ[R] Target R hI :=
  LaurentPolynomialUniversal.lift (Algebra.ofId R (Target R hI)) (targetUnit R hI (leftClass hI))

def rawMap : Torus (Laurent R) (Representatives n I) →ₐ[R] Target R hI :=
  FinsuppTorusTower.lift R (Laurent R) _ (frozenMap R hI) (targetUnit R hI)

theorem raw_coordinate (p : Representatives n I) : rawMap R hI (torusCoordinate (Laurent R) _ p)=
    (targetUnit R hI p : Target R hI) := FinsuppTorusTower.lift_coordinate R _ _ _ _ p

theorem raw_coefficient (s : Laurent R) : rawMap R hI (algebraMap (Laurent R) _ s)=frozenMap R hI s :=
  FinsuppTorusTower.lift_coefficient R _ _ _ _ s

theorem raw_endpoint (e : Bool) :
    rawMap R hI (torusCoordinate (Laurent R) _ (compress hI (endpoint hI e)))=
      frozenMap R hI (endpointValue (Laurent R) (n:=n) (parameter R) 1 e) := by
  rw [raw_coordinate]
  cases e
  · change (targetUnit R hI (leftClass hI) : Target R hI)=frozenMap R hI (parameter R)
    exact (LaurentPolynomialUniversal.lift_parameter _ _).symm
  · change (targetUnit R hI (rightClass hI) : Target R hI)=frozenMap R hI ((-1:Laurent R)^((n+1)/2)*1)
    simp [targetUnit,map_mul,map_pow,map_neg,map_one]

def forward : Source R hI →ₐ[R] Target R hI :=
  Ideal.Quotient.liftₐ (endpointIdeal (Laurent R) hI (parameter R) 1) (rawMap R hI) (by
    change endpointIdeal (Laurent R) hI (parameter R) 1 ≤ RingHom.ker (rawMap R hI).toRingHom
    apply Ideal.span_le.mpr
    rintro _ ⟨e,rfl⟩
    change rawMap R hI (_-_)=0
    rw [map_sub,raw_endpoint,raw_coefficient,sub_self])

def quotientCoordinate (p : Representatives n I) : Source R hI :=
  Ideal.Quotient.mk (endpointIdeal (Laurent R) hI (parameter R) 1) (torusCoordinate (Laurent R) _ p)

def quotientUnit (p : Representatives n I) : (Source R hI)ˣ :=
  Units.map (Ideal.Quotient.mk (endpointIdeal (Laurent R) hI (parameter R) 1)).toMonoidHom
    (unit (Laurent R) _ p)

theorem endpoint_relation (e : Bool) : quotientCoordinate R hI (compress hI (endpoint hI e))=
    algebraMap (Laurent R) (Source R hI) (endpointValue (Laurent R) (n:=n) (parameter R) 1 e) :=
  signed_endpoint (Laurent R) hI (parameter R) 1 e

theorem forward_coordinate (p : Representatives n I) : forward R hI (quotientCoordinate R hI p)=
    (targetUnit R hI p : Target R hI) := raw_coordinate R hI p

theorem forward_coefficient (s : Laurent R) : forward R hI (algebraMap (Laurent R) (Source R hI) s)=frozenMap R hI s :=
  raw_coefficient R hI s

def backward : Target R hI →ₐ[R] Source R hI :=
  FinsuppTorusUniversal.lift R _ (fun p => quotientUnit R hI p.val)

theorem backward_coordinate (p : FreeCoordinates hI) : backward R hI (torusCoordinate R _ p)=
    quotientCoordinate R hI p.val := FinsuppTorusUniversal.lift_coordinate R _ _ p

theorem backward_target (p : Representatives n I) : backward R hI (targetUnit R hI p : Target R hI)=
    quotientCoordinate R hI p := by
  rw [targetUnit]
  split_ifs with hp
  · subst p
    have he := endpoint_relation R hI true
    change quotientCoordinate R hI (rightClass hI)=algebraMap (Laurent R) (Source R hI) ((-1:Laurent R)^((n+1)/2)*1) at he
    rw [he]
    simp only [Units.val_pow_eq_pow_val,Units.val_neg,Units.val_one,map_pow,map_neg,map_one,map_mul,mul_one]
  · exact backward_coordinate R hI ⟨p,hp⟩

#print axioms leftClass
#print axioms rightClass
#print axioms FreeCoordinates
#print axioms Target
#print axioms Source
#print axioms targetUnit
#print axioms frozenMap
#print axioms rawMap
#print axioms raw_coordinate
#print axioms raw_coefficient
#print axioms raw_endpoint
#print axioms forward
#print axioms quotientCoordinate
#print axioms quotientUnit
#print axioms endpoint_relation
#print axioms forward_coordinate
#print axioms forward_coefficient
#print axioms backward
#print axioms backward_coordinate
#print axioms backward_target
end Verification.PathVariableEndpointMaps
