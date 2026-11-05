/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RostUnitTransport
import Verification.RostComponentEvaluation

/-!
# Rost Boundary Transport Values

Generic values of a principal boundary survive the specified source
and target ring changes. The formula uses the actual transported unit and
the actual comap of the target generic point.
-/
noncomputable section
namespace Verification.RostBoundaryTransportValues
open CategoryTheory AlgebraicGeometry
open Verification.RostCanonicalCoefficients
open Verification.RostPrincipalLocalizationInput (OpenRing ClosedRing)
open Verification.RostPrincipalResidueInput
variable (T : RostAffineInput.Theory) (P : RostPrincipalLocalizationInput.Theory T)
variable (F : RostFiniteProducts.Standard T) (Z : RostWeightZero.IntegralConvention T)
variable (E : GenericZeroEvaluation T F Z) (U : OriginalRostUnitTerms.UnitsConvention T)
variable (UN : UnitsNaturality T F U)
variable (k A B C : Type) [Field k] [CommRing A] [CommRing B] [CommRing C]
variable [Algebra k A] [Algebra.Smooth k A] [Algebra k B] [Algebra.Smooth k B]
variable (t : A) (ht : IsRegular t) [Algebra.Smooth k (OpenRing A t)]
variable (es : B ≃+* OpenRing A t) (et : ClosedRing A t ≃+* C)

include UN in
theorem generic_value (q : PrimeSpectrum C) (hq : q.asIdeal ∈ minimalPrimes C)
    (a : Sections T B 1) :
    E.value C q hq
      (transport T et 0 (P.boundary k A t ht 1 (transport T es 1 a))) =
    genericResidue T P F Z E U k A t ht
      (PrimeSpectrum.comap et.toRingHom q) (transportPoint_minimal et q hq)
      (Additive.ofMul (Units.map es.toMonoidHom
        (Additive.toMul ((U.units k B).hom a)))) := by
  rw [E.iso (ClosedRing A t) C et q hq (transportPoint_minimal et q hq)]
  rw [RostUnitTransport.boundary_transport T F U UN k B A P t ht es a]
  rfl

include UN in
theorem component_value {J : Type} [Fintype J] (D : J → Type)
    [∀ j,CommRing (D j)] [∀ j,IsDomain (D j)] (e : C ≃+* ∀ j,D j) (j : J)
    (a : Sections T B 1) :
    (RostComponentZero.componentIso T F Z D e).hom
      (transport T et 0 (P.boundary k A t ht 1 (transport T es 1 a)))
      (ConnectedComponents.mk (RostComponentEvaluation.point D e j)) =
    genericResidue T P F Z E U k A t ht
      (PrimeSpectrum.comap et.toRingHom (RostComponentEvaluation.point D e j))
      (transportPoint_minimal et _ (RostComponentEvaluation.point_minimal D e j))
      (Additive.ofMul (Units.map es.toMonoidHom
        (Additive.toMul ((U.units k B).hom a)))) := by
  rw [← RostComponentEvaluation.component_value T F Z E D e j]
  exact generic_value T P F Z E U UN k A B C t ht es et _ _ a

#print axioms generic_value
#print axioms component_value
end Verification.RostBoundaryTransportValues
