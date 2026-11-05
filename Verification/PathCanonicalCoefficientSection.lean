/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathYWordBasis
import Verification.PathZWordBasis

/-!
# Path Canonical Coefficient Section

Explicit algebra sections of the genuine original partner-zero
projections. They agree with the literal path coefficient inclusions.
The coefficient smoothness is obtained from the constructed endpoint tori.
-/
noncomputable section
set_option quotPrecheck false
namespace Verification.PathCanonicalCoefficientSection
open Verification.PathCompression Verification.PathLiteralStratum
open Verification.PathSignedStratumCoefficients Verification.PathOriginalStratumTransport
open Verification.PathOriginalIndependence
variable (R : Type) [CommRing R] {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)

def y_section : PathOriginalCoefficientTransport.Fiber (I:=I) R Empty (PathOriginalYPresentation.matrix n) →ₐ[R]
    GlobalNormalFrame.ZeroLayer R Empty n (mutableSet n I) (PathOriginalYPresentation.matrix n) :=
  (PathOriginalYStratum.equiv R hI).toAlgHom.comp
    ((toLayer R hI (1:R) 1).comp (PathOriginalYCoefficient.coefficientEquiv R hI).symm.toAlgHom)

theorem y_split : (OriginalCanonicalFiberProjection.projection R Empty n (mutableSet n I)
    (PathOriginalYPresentation.matrix n)
    (positive_order _ y_mutable) (negative_order _ y_mutable)
    (support _ y_mutable) (independent _ y_mutable hI)).comp
      (y_section R hI)=AlgHom.id R _ := by
  ext c
  change OriginalCanonicalFiberProjection.projection R Empty n (mutableSet n I) (PathOriginalYPresentation.matrix n)
    _ _ _ _ ((PathOriginalYStratum.equiv R hI) (toLayer R hI (1:R) 1
      ((PathOriginalYCoefficient.coefficientEquiv R hI).symm c)))=c
  rw [←PathOriginalYCoefficient.projection,PathCoefficientProjection.projection_section,AlgEquiv.apply_symm_apply]

theorem y_inclusion : (y_section R hI).comp (PathOriginalYCoefficient.coefficientEquiv R hI).toAlgHom=
    (PathOriginalYStratum.equiv R hI).toAlgHom.comp (toLayer R hI (1:R) 1) := by
  ext c
  change PathOriginalYStratum.equiv R hI (toLayer R hI (1:R) 1
    ((PathOriginalYCoefficient.coefficientEquiv R hI).symm ((PathOriginalYCoefficient.coefficientEquiv R hI) c)))=_
  rw [AlgEquiv.symm_apply_apply]
  rfl

def z_section : PathOriginalCoefficientTransport.Fiber (I:=I) R (Fin 1) (PathOriginalZPresentation.matrix n) →ₐ[R]
    GlobalNormalFrame.ZeroLayer R (Fin 1) n (mutableSet n I) (PathOriginalZPresentation.matrix n) :=
  (PathOriginalZStratum.equiv R hI).toAlgHom.comp
    (((toLayer (PathOriginalZPresentation.Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1).restrictScalars R).comp
      (PathOriginalZCoefficient.coefficientEquiv R hI).symm.toAlgHom)

theorem z_split : (OriginalCanonicalFiberProjection.projection R (Fin 1) n (mutableSet n I)
    (PathOriginalZPresentation.matrix n)
    (positive_order _ z_mutable) (negative_order _ z_mutable)
    (support _ z_mutable) (independent _ z_mutable hI)).comp
      (z_section R hI)=AlgHom.id R _ := by
  ext c
  change OriginalCanonicalFiberProjection.projection R (Fin 1) n (mutableSet n I) (PathOriginalZPresentation.matrix n)
    _ _ _ _ ((PathOriginalZStratum.equiv R hI) (toLayer (PathOriginalZPresentation.Coefficient R) hI
      (LaurentPolynomialUniversal.parameter R) 1 ((PathOriginalZCoefficient.coefficientEquiv R hI).symm c)))=c
  rw [←PathOriginalZCoefficient.projection,PathCoefficientProjection.projection_section,AlgEquiv.apply_symm_apply]

theorem z_inclusion : (z_section R hI).comp (PathOriginalZCoefficient.coefficientEquiv R hI).toAlgHom=
    (PathOriginalZStratum.equiv R hI).toAlgHom.comp
      ((toLayer (PathOriginalZPresentation.Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1).restrictScalars R) := by
  ext c
  change PathOriginalZStratum.equiv R hI (toLayer (PathOriginalZPresentation.Coefficient R) hI
    (LaurentPolynomialUniversal.parameter R) 1
    ((PathOriginalZCoefficient.coefficientEquiv R hI).symm ((PathOriginalZCoefficient.coefficientEquiv R hI) c)))=_
  rw [AlgEquiv.symm_apply_apply]
  rfl

include hI in
theorem z_fiber_smooth : Algebra.Smooth R
    (PathOriginalCoefficientTransport.Fiber (I:=I) R (Fin 1) (PathOriginalZPresentation.matrix n)) := by
  classical
  letI:=TorusSmooth.torus_smooth R (PathVariableEndpointMaps.FreeCoordinates hI)
  exact Algebra.Smooth.of_equiv (PathZWordBasis.torusEquiv R hI).symm

theorem y_fiber_smooth {d : ℕ} (hY : Admissible (2*d) I) : Algebra.Smooth R
    (PathOriginalCoefficientTransport.Fiber (I:=I) R Empty (PathOriginalYPresentation.matrix (2*d))) := by
  classical
  letI:=TorusSmooth.torus_smooth R (PathEvenEndpointTorus.FreeCoordinates hY)
  exact Algebra.Smooth.of_equiv (PathYWordBasis.torusEquiv R hY).symm

#print axioms y_section
#print axioms y_split
#print axioms y_inclusion
#print axioms z_section
#print axioms z_split
#print axioms z_inclusion
#print axioms z_fiber_smooth
#print axioms y_fiber_smooth
end Verification.PathCanonicalCoefficientSection
