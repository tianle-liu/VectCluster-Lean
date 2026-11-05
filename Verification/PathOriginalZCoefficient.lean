/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOriginalCoefficientTransport
import Verification.PathOriginalIndependence

/-!
# Path Original Z Coefficient

The Z path compressed coefficients are the literal canonical fiber of
its original zero layer, by quotienting the same selected original partners.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
namespace Verification.PathOriginalZCoefficient
open Verification.PathCompression Verification.PathLiteralStratum Verification.PathClassRepresentatives
open Verification.PathSignedStratumCoefficients Verification.PathCoefficientProjection
open Verification.PathOriginalStratumTransport Verification.PathOriginalIndependence
open Verification.PathOriginalZPresentation
variable (R : Type) [CommRing R] {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)

theorem selected_partner (i : I) : PathOriginalZStratum.equiv R hI (layerY (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 (mutableIndex hI i))=
    OriginalFiberPartnerProjection.partner R (Fin 1) n (mutableSet n I) (matrix n) (selectedEquiv hI i) :=
  PathOriginalZStratum.equiv_y R hI (mutableIndex hI i)

def coefficientEquiv : Coefficients (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 ≃ₐ[R]
    PathOriginalCoefficientTransport.Fiber (I := I) R (Fin 1) (matrix n) :=
  PathOriginalCoefficientTransport.coefficientEquiv R (Coefficient R) (Fin 1) hI (LaurentPolynomialUniversal.parameter R) 1 (matrix n)
    (PathOriginalZStratum.equiv R hI) (selected_partner R hI)
    (positive_order _ z_mutable) (negative_order _ z_mutable) (support _ z_mutable)
    (independent _ z_mutable hI)

theorem projection (c : Layer (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1) :
    coefficientEquiv R hI (PathCoefficientProjection.projection hI (Coefficient R) (LaurentPolynomialUniversal.parameter R) 1 c)=
      OriginalCanonicalFiberProjection.projection R (Fin 1) n (mutableSet n I) (matrix n)
        (positive_order _ z_mutable) (negative_order _ z_mutable) (support _ z_mutable)
        (independent _ z_mutable hI) (PathOriginalZStratum.equiv R hI c) :=
  PathOriginalCoefficientTransport.coefficientEquiv_projection R (Coefficient R) (Fin 1) hI (LaurentPolynomialUniversal.parameter R) 1 (matrix n)
    (PathOriginalZStratum.equiv R hI) (selected_partner R hI)
    (positive_order _ z_mutable) (negative_order _ z_mutable) (support _ z_mutable)
    (independent _ z_mutable hI) c

theorem signed (p : Vertices n I) :
    coefficientEquiv R hI (signedCoordinate (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 p : Coefficients (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1)=
      OriginalCanonicalFiberProjection.projection R (Fin 1) n (mutableSet n I) (matrix n)
        (positive_order _ z_mutable) (negative_order _ z_mutable) (support _ z_mutable)
        (independent _ z_mutable hI) (PathOriginalZStratum.equiv R hI
          (signedUnit (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 p : Layer (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1)) := by
  rw [← PathCoefficientProjection.projection_signed hI (Coefficient R) (LaurentPolynomialUniversal.parameter R) 1 p,projection]

#print axioms selected_partner
#print axioms coefficientEquiv
#print axioms projection
#print axioms signed
end Verification.PathOriginalZCoefficient
