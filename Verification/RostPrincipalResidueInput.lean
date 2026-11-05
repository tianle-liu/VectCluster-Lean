/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RostCanonicalCoefficients
import Verification.RostPrincipalLocalizationInput
import Verification.DVRFractionOrder
import Mathlib.RingTheory.Localization.AtPrime

/-!
# Rost Principal Residue Input

Ordinary K^M_1 principal residues normalized by the actual generic
DVR valuation. In a regular chart its local ring is the normalization
branch and its residue field is the target generic field; this is the
usual residue/norm definition in this regular case. No assertion about
an exchange coordinate or its multiplicity is supplied as input.
-/
noncomputable section
namespace Verification.RostPrincipalResidueInput
open CategoryTheory AlgebraicGeometry
open Verification.RostCanonicalCoefficients
open Verification.RostPrincipalLocalizationInput (OpenRing ClosedRing)
variable (T : RostAffineInput.Theory) (P : RostPrincipalLocalizationInput.Theory T)
variable (F : RostFiniteProducts.Standard T) (Z : RostWeightZero.IntegralConvention T)
variable (E : GenericZeroEvaluation T F Z) (U : OriginalRostUnitTerms.UnitsConvention T)

variable (k A : Type) [Field k] [CommRing A] [Algebra k A] [Algebra.Smooth k A]
variable (t : A) (ht : IsRegular t)
variable [Algebra.Smooth k (OpenRing A t)]

def unitBoundary : Additive (OpenRing A t)ˣ →+ Sections T (ClosedRing A t) 0 :=
  ((U.units k (OpenRing A t)).inv ≫ P.boundary k A t ht 1).hom

def genericResidue (q : PrimeSpectrum (ClosedRing A t))
    (hq : q.asIdeal ∈ minimalPrimes (ClosedRing A t)) :
    Additive (OpenRing A t)ˣ →+ ℤ :=
  (E.value (ClosedRing A t) q hq).comp (unitBoundary T P U k A t ht)

omit [Field k] [Algebra k A] [Algebra.Smooth k A]
  [Algebra.Smooth k (OpenRing A t)] in
def sourcePrime (q : PrimeSpectrum (ClosedRing A t)) : PrimeSpectrum A :=
  PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {t})) q

omit [Field k] [Algebra k A] [Algebra.Smooth k A]
  [Algebra.Smooth k (OpenRing A t)] in
abbrev Local (q : PrimeSpectrum (ClosedRing A t)) :=
  Localization.AtPrime (sourcePrime A t q).asIdeal

/-- The cited ordinary normalization, uniform in every regular principal
pair and actual closed generic point. Smoothness of the open is stated
explicitly to use the already chosen units comparison. The displayed
integer order was constructed from mathlib's genuine adic valuation. -/
structure Normalization : Prop where
  dvr : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] [Algebra.Smooth k A]
    (t : A) (ht : IsRegular t) [Algebra.Smooth k (OpenRing A t)]
    (q : PrimeSpectrum (ClosedRing A t)) (hq : q.asIdeal ∈ minimalPrimes (ClosedRing A t))
    [IsDomain (Local A t q)] [IsDiscreteValuationRing (Local A t q)]
    (hnt : algebraMap A (Local A t q) t ≠ 0) (u : Additive (OpenRing A t)ˣ),
    genericResidue T P F Z E U k A t ht q hq u =
      DVRFractionOrder.openOrder (Local A t q) (FractionRing (Local A t q))
        t (algebraMap A (Local A t q)) hnt u

variable (N : Normalization T P F Z E U)
variable (q : PrimeSpectrum (ClosedRing A t)) (hq : q.asIdeal ∈ minimalPrimes (ClosedRing A t))
variable [IsDomain (Local A t q)] [IsDiscreteValuationRing (Local A t q)]
variable (hnt : algebraMap A (Local A t q) t ≠ 0)

include N hnt in
theorem residue_parameter (u : (OpenRing A t)ˣ)
    (hu : (u : OpenRing A t) = algebraMap A (OpenRing A t) t)
    (hgen : IsLocalRing.maximalIdeal (Local A t q) =
      Ideal.span {algebraMap A (Local A t q) t}) :
    genericResidue T P F Z E U k A t ht q hq (Additive.ofMul u) = 1 := by
  rw [N.dvr k A t ht q hq hnt]
  exact DVRFractionOrder.openOrder_parameter _ _ _ _ _ u hu hgen

include N hnt in
theorem residue_not_mem (u : (OpenRing A t)ˣ) (a : A)
    (hu : (u : OpenRing A t) = algebraMap A (OpenRing A t) a)
    (ha : a ∉ (sourcePrime A t q).asIdeal) :
    genericResidue T P F Z E U k A t ht q hq (Additive.ofMul u) = 0 := by
  rw [N.dvr k A t ht q hq hnt]
  apply DVRFractionOrder.openOrder_not_mem _ _ _ _ _ u a hu
  intro h
  apply ha
  change a ∈ (IsLocalRing.maximalIdeal (Local A t q)).comap (algebraMap A (Local A t q)) at h
  rw [IsLocalization.AtPrime.comap_maximalIdeal (Local A t q) (sourcePrime A t q).asIdeal] at h
  exact h

include N hnt in
/-- Unit extension across the divisor forces zero residue. This is an
internal consequence of the ordinary normalization and the actual local ring. -/
theorem residue_extended_unit (u : Aˣ) :
    genericResidue T P F Z E U k A t ht q hq
      (Additive.ofMul (Units.map (algebraMap A (OpenRing A t)).toMonoidHom u)) = 0 := by
  apply residue_not_mem T P F Z E U k A t ht N q hq hnt _ (u : A) rfl
  intro hu
  have htop := Ideal.eq_top_of_isUnit_mem (sourcePrime A t q).asIdeal hu u.isUnit
  exact (sourcePrime A t q).isPrime.ne_top htop

omit [IsDomain (Local A t q)] [IsDiscreteValuationRing (Local A t q)] in
theorem residue_zpow (u : (OpenRing A t)ˣ) (n : ℤ) :
    genericResidue T P F Z E U k A t ht q hq (Additive.ofMul (u ^ n)) =
      n * genericResidue T P F Z E U k A t ht q hq (Additive.ofMul u) := by
  change genericResidue T P F Z E U k A t ht q hq (n • Additive.ofMul u) = _
  simp only [map_zsmul,zsmul_eq_mul,Int.cast_id]

#print axioms unitBoundary
#print axioms genericResidue
#print axioms sourcePrime
#print axioms Local
#print axioms Normalization
#print axioms residue_parameter
#print axioms residue_not_mem
#print axioms residue_extended_unit
#print axioms residue_zpow
end Verification.RostPrincipalResidueInput
