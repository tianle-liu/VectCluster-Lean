/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathCoefficientProjection
import Verification.ScaledPolynomialProjection

/-!
# Path Coefficient Quotient

The canonical signed path coefficient algebra is the genuine quotient
of the path layer by all selected original partners.
-/
noncomputable section
namespace Verification.PathCoefficientQuotient
open Verification.PathCompression Verification.PathLiteralStratum
open Verification.PathSignedStratumCoefficients Verification.PathSignedStratumEquivalence
open Verification.PathCoefficientProjection MvPolynomial
variable (R : Type) [CommRing R] {n : ℕ} {I : Finset ℕ} (hI : Admissible n I) (a b : R)

def equiv : (Layer R hI a b ⧸ partnerIdeal hI R a b) ≃ₐ[R] Coefficients R hI a b :=
  ScaledPolynomialProjection.quotientEquiv (stratumEquiv R hI a b)
    (fun i : I => layerY R hI a b (mutableIndex hI i)) (fun _ => 1)
    (fun i => by simpa only [Units.val_one,map_one,one_mul] using stratumEquiv_partner R hI a b i)

theorem equiv_mk (a' : Layer R hI a b) :
    equiv R hI a b (Ideal.Quotient.mk (partnerIdeal hI R a b) a')=projection hI R a b a' :=
  ScaledPolynomialProjection.quotientEquiv_mk _ _ _ _ a'

#print axioms equiv
#print axioms equiv_mk
end Verification.PathCoefficientQuotient
