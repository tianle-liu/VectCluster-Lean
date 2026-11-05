/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathVariableEndpointMaps
import Verification.PathSignedStratumEquivalence

/-!
# Path Variable Endpoint Torus

The actual Z stratum over the ground ring: the freely variable left
endpoint eliminates its own Laurent coefficient and only the right class
is specialized. Exact signed original coordinates are retained.
-/
noncomputable section
namespace Verification.PathVariableEndpointTorus
open Classical Verification.PathCompression Verification.PathClassRepresentatives
open Verification.PathVariableEndpointMaps Verification.LaurentPolynomialUniversal
open Verification.OriginalTorus Verification.FinsuppTorusUniversal
open Verification.PathSignedStratumCoefficients Verification.PathLiteralStratum MvPolynomial
variable (R : Type) [CommRing R] {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)

theorem backward_frozen : (backward R hI).comp (frozenMap R hI)=
    IsScalarTower.toAlgHom R (Laurent R) (Source R hI) := by
  apply LaurentPolynomialUniversal.hom_ext
  · intro r
    change backward R hI (frozenMap R hI (algebraMap R (Laurent R) r))=algebraMap R _ r
    rw [AlgHom.commutes,AlgHom.commutes]
  · change backward R hI (frozenMap R hI (parameter R))=algebraMap (Laurent R) _ (parameter R)
    rw [frozenMap,LaurentPolynomialUniversal.lift_parameter,backward_target]
    exact endpoint_relation R hI false

theorem backward_forward : (backward R hI).comp (forward R hI)=AlgHom.id R _ := by
  apply Ideal.Quotient.algHom_ext
  apply FinsuppTorusTower.hom_ext R (Laurent R) (Representatives n I)
  · intro s
    change backward R hI (forward R hI (algebraMap (Laurent R) (Source R hI) s))=algebraMap (Laurent R) _ s
    rw [forward_coefficient]
    exact AlgHom.congr_fun (backward_frozen R hI) s
  · intro p
    change backward R hI (forward R hI (quotientCoordinate R hI p))=quotientCoordinate R hI p
    rw [forward_coordinate,backward_target]

theorem forward_backward : (forward R hI).comp (backward R hI)=AlgHom.id R _ := by
  apply FinsuppTorusUniversal.hom_ext
  intro p
  change forward R hI (backward R hI (torusCoordinate R _ p))=torusCoordinate R _ p
  rw [backward_coordinate,forward_coordinate,targetUnit,dif_neg p.property]
  rfl

def coefficientEquiv : Source R hI ≃ₐ[R] Target R hI :=
  AlgEquiv.ofAlgHom (forward R hI) (backward R hI) (forward_backward R hI) (backward_forward R hI)

theorem coefficient_coordinate (p : Representatives n I) : coefficientEquiv R hI (quotientCoordinate R hI p)=
    (targetUnit R hI p : Target R hI) := forward_coordinate R hI p

theorem coefficient_free (p : FreeCoordinates hI) : coefficientEquiv R hI (quotientCoordinate R hI p.val)=
    torusCoordinate R _ p := by
  rw [coefficient_coordinate,targetUnit,dif_neg p.property]
  rfl

def stratumEquiv : Layer (Laurent R) hI (parameter R) 1 ≃ₐ[R]
    MvPolynomial I (Torus R (FreeCoordinates hI)) :=
  ((PathSignedStratumEquivalence.stratumEquiv (Laurent R) hI (parameter R) 1).restrictScalars R).trans
    (MvPolynomial.mapAlgEquiv I (coefficientEquiv R hI))

theorem stratum_partner (i : I) :
    stratumEquiv R hI (layerY (Laurent R) hI (parameter R) 1 (mutableIndex hI i))=X i := by
  change MvPolynomial.map (coefficientEquiv R hI).toRingHom
    (PathSignedStratumEquivalence.stratumEquiv (Laurent R) hI (parameter R) 1
      (layerY (Laurent R) hI (parameter R) 1 (mutableIndex hI i)))=_
  rw [PathSignedStratumEquivalence.stratumEquiv_partner,MvPolynomial.map_X]

theorem stratum_free_coordinate (p : FreeCoordinates hI) :
    stratumEquiv R hI (signedUnit (Laurent R) hI (parameter R) 1 (includeRepresentative p.val) :
      Layer (Laurent R) hI (parameter R) 1)=C (torusCoordinate R _ p) := by
  change MvPolynomial.map (coefficientEquiv R hI).toRingHom
    (PathSignedStratumEquivalence.stratumEquiv (Laurent R) hI (parameter R) 1
      (signedUnit (Laurent R) hI (parameter R) 1 (includeRepresentative p.val) : Layer (Laurent R) hI (parameter R) 1))=_
  rw [PathSignedStratumEquivalence.stratumEquiv_signed,MvPolynomial.map_C]
  change C (coefficientEquiv R hI (quotientCoordinate R hI (compress hI (includeRepresentative p.val))))=_
  rw [compress_include,coefficient_free]

omit [CommRing R] in
theorem rank_formula : Fintype.card (FreeCoordinates hI)+2*I.card=n+1 := by
  have hc : Fintype.card (Representatives n I)=(available I (n+2)).card := Fintype.card_coe _
  have he : Fintype.card {p : Representatives n I // p=rightClass hI}=1 := by
    apply Fintype.card_eq_one_iff.mpr
    refine ⟨⟨rightClass hI,rfl⟩,?_⟩
    rintro ⟨p,hp⟩
    subst p
    rfl
  have hp : 0<(available I (n+2)).card := Finset.card_pos.mpr ⟨0,zero_available hI (by omega)⟩
  have hr := available_card hI
  change Fintype.card {p : Representatives n I // ¬p=rightClass hI}+2*I.card=n+1
  rw [Fintype.card_subtype_compl,he,hc]
  omega

#print axioms backward_frozen
#print axioms backward_forward
#print axioms forward_backward
#print axioms coefficientEquiv
#print axioms coefficient_coordinate
#print axioms coefficient_free
#print axioms stratumEquiv
#print axioms stratum_partner
#print axioms stratum_free_coordinate
#print axioms rank_formula
end Verification.PathVariableEndpointTorus
