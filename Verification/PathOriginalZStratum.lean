/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOriginalStratumTransport
import Verification.PathOriginalZEquivalence

/-!
# Path Original Z Stratum

The actual one-frozen-coordinate Z zero layer is the Laurent-coefficient
path layer, preserving both mutable generators and the actual frozen unit.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
namespace Verification.PathOriginalZStratum
open Verification.PathCompression Verification.PathLiteralStratum
open Verification.PathOriginalStratumTransport Verification.PathOriginalZPresentation
variable (R : Type) [CommRing R] {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)

theorem parameter_isUnit : IsUnit (LaurentPolynomialUniversal.parameter R) := by
  simpa only [LaurentPolynomialUniversal.parameterUnit_val] using
    (LaurentPolynomialUniversal.parameterUnit R).isUnit

def ringEquiv : Layer (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 ≃+*
    Verification.GlobalNormalFrame.ZeroLayer R (Fin 1) n (mutableSet n I) (matrix n) :=
  PathOriginalStratumTransport.equiv hI (Coefficient R) R (Fin 1)
    (LaurentPolynomialUniversal.parameter R) 1 (parameter_isUnit R) isUnit_one (matrix n)
    (PathOriginalZEquivalence.equiv R n).toRingEquiv (PathOriginalZEquivalence.equiv_x R n)

def equiv : Layer (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 ≃ₐ[R]
    Verification.GlobalNormalFrame.ZeroLayer R (Fin 1) n (mutableSet n I) (matrix n) :=
  AlgEquiv.ofRingEquiv (f := ringEquiv R hI) (fun r => by
    have hh := PathOriginalStratumTransport.toOriginal_base hI (Coefficient R) R (Fin 1)
      (LaurentPolynomialUniversal.parameter R) 1 (parameter_isUnit R) isUnit_one
      (matrix n) (PathOriginalZEquivalence.equiv R n).toRingEquiv (PathOriginalZEquivalence.equiv_x R n)
      (algebraMap R (Path R n) r)
    change ringEquiv R hI (algebraMap R (Layer (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1) r) =
      Verification.OriginalStratumUniversal.baseMap R (Fin 1) n (mutableSet n I) (matrix n)
        (PathOriginalZEquivalence.equiv R n (algebraMap R (Path R n) r)) at hh
    rw [AlgEquiv.commutes,Verification.OriginalStratumUniversal.base_scalar] at hh
    exact hh)

theorem equiv_x (i : Fin n) : equiv R hI (layerX (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 i)=
    Verification.OriginalStratumUniversal.baseMap R (Fin 1) n (mutableSet n I) (matrix n)
      (Verification.FrozenAcyclicCover.initial R (Fin 1) n (matrix n) (Sum.inl i)) :=
  PathOriginalStratumTransport.equiv_x hI (Coefficient R) R (Fin 1)
    (LaurentPolynomialUniversal.parameter R) 1 (parameter_isUnit R) isUnit_one (matrix n)
    (PathOriginalZEquivalence.equiv R n).toRingEquiv (PathOriginalZEquivalence.equiv_x R n) i

theorem equiv_y (i : Fin n) : equiv R hI (layerY (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1 i)=
    Verification.OriginalStratumUniversal.baseMap R (Fin 1) n (mutableSet n I) (matrix n)
      (Verification.FrozenAcyclicCover.mutated R (Fin 1) n (matrix n) i) := by
  change PathOriginalStratumTransport.toOriginal hI (Coefficient R) R (Fin 1)
    (LaurentPolynomialUniversal.parameter R) 1 (parameter_isUnit R) isUnit_one (matrix n)
    (PathOriginalZEquivalence.equiv R n).toRingEquiv (PathOriginalZEquivalence.equiv_x R n)
      (PathStratumRingUniversal.baseMap (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1
        (Verification.PathPresentation.y (LaurentPolynomialUniversal.parameter R) 1 i)) = _
  rw [PathOriginalStratumTransport.toOriginal_base]
  change Verification.OriginalStratumUniversal.baseMap R (Fin 1) n (mutableSet n I) (matrix n)
    (PathOriginalZEquivalence.equiv R n (Verification.PathPresentation.y (LaurentPolynomialUniversal.parameter R) 1 i)) = _
  rw [PathOriginalZEquivalence.equiv_y]

theorem equiv_parameter : equiv R hI
    (algebraMap (Coefficient R) (Layer (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1)
      (LaurentPolynomialUniversal.parameter R)) =
    Verification.OriginalStratumUniversal.baseMap R (Fin 1) n (mutableSet n I) (matrix n)
      (Verification.FrozenAcyclicCover.initial R (Fin 1) n (matrix n) (Sum.inr 0)) := by
  have hh := PathOriginalStratumTransport.toOriginal_base hI (Coefficient R) R (Fin 1)
    (LaurentPolynomialUniversal.parameter R) 1 (parameter_isUnit R) isUnit_one
    (matrix n) (PathOriginalZEquivalence.equiv R n).toRingEquiv (PathOriginalZEquivalence.equiv_x R n)
    (algebraMap (Coefficient R) (Path R n) (LaurentPolynomialUniversal.parameter R))
  change equiv R hI
    (algebraMap (Coefficient R) (Layer (Coefficient R) hI (LaurentPolynomialUniversal.parameter R) 1)
      (LaurentPolynomialUniversal.parameter R)) =
    Verification.OriginalStratumUniversal.baseMap R (Fin 1) n (mutableSet n I) (matrix n)
      (PathOriginalZEquivalence.equiv R n
        (algebraMap (Coefficient R) (Path R n) (LaurentPolynomialUniversal.parameter R))) at hh
  rw [PathOriginalZEquivalence.equiv_parameter] at hh
  exact hh

#print axioms parameter_isUnit
#print axioms ringEquiv
#print axioms equiv
#print axioms equiv_x
#print axioms equiv_y
#print axioms equiv_parameter
end Verification.PathOriginalZStratum
