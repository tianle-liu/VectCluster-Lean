/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOriginalCoefficientTransport
import Verification.PathOriginalIndependence

/-!
# Path Original Y Coefficient

The Y path compressed coefficients are the literal canonical fiber of
its original zero layer, by quotienting the same selected original partners.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
namespace Verification.PathOriginalYCoefficient
open Verification.PathCompression Verification.PathLiteralStratum Verification.PathClassRepresentatives
open Verification.PathSignedStratumCoefficients Verification.PathCoefficientProjection
open Verification.PathOriginalStratumTransport Verification.PathOriginalIndependence
open Verification.PathOriginalYPresentation
variable (R : Type) [CommRing R] {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)

theorem selected_partner (i : I) : PathOriginalYStratum.equiv R hI (layerY R hI 1 1 (mutableIndex hI i))=
    OriginalFiberPartnerProjection.partner R Empty n (mutableSet n I) (matrix n) (selectedEquiv hI i) :=
  PathOriginalYStratum.equiv_y R hI (mutableIndex hI i)

def coefficientEquiv : Coefficients R hI (1:R) 1 ≃ₐ[R]
    PathOriginalCoefficientTransport.Fiber (I := I) R Empty (matrix n) :=
  PathOriginalCoefficientTransport.coefficientEquiv R R Empty hI 1 1 (matrix n)
    (PathOriginalYStratum.equiv R hI) (selected_partner R hI)
    (positive_order _ y_mutable) (negative_order _ y_mutable) (support _ y_mutable)
    (independent _ y_mutable hI)

theorem projection (c : Layer R hI (1:R) 1) :
    coefficientEquiv R hI (PathCoefficientProjection.projection hI R 1 1 c)=
      OriginalCanonicalFiberProjection.projection R Empty n (mutableSet n I) (matrix n)
        (positive_order _ y_mutable) (negative_order _ y_mutable) (support _ y_mutable)
        (independent _ y_mutable hI) (PathOriginalYStratum.equiv R hI c) :=
  PathOriginalCoefficientTransport.coefficientEquiv_projection R R Empty hI 1 1 (matrix n)
    (PathOriginalYStratum.equiv R hI) (selected_partner R hI)
    (positive_order _ y_mutable) (negative_order _ y_mutable) (support _ y_mutable)
    (independent _ y_mutable hI) c

theorem signed (p : Vertices n I) :
    coefficientEquiv R hI (signedCoordinate R hI (1:R) 1 p : Coefficients R hI (1:R) 1)=
      OriginalCanonicalFiberProjection.projection R Empty n (mutableSet n I) (matrix n)
        (positive_order _ y_mutable) (negative_order _ y_mutable) (support _ y_mutable)
        (independent _ y_mutable hI) (PathOriginalYStratum.equiv R hI
          (signedUnit R hI (1:R) 1 p : Layer R hI (1:R) 1)) := by
  rw [← PathCoefficientProjection.projection_signed hI R (1:R) 1 p,projection]

#print axioms selected_partner
#print axioms coefficientEquiv
#print axioms projection
#print axioms signed
end Verification.PathOriginalYCoefficient
