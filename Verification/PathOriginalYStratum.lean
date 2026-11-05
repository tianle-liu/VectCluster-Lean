/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOriginalStratumTransport
import Verification.PathOriginalYPresentation

/-!
# Path Original Y Stratum

The signed-compression path stratum is the literal original Y zero layer,
with its scalar, original and partner coordinates preserved.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
namespace Verification.PathOriginalYStratum
open Verification.PathCompression Verification.PathLiteralStratum
open Verification.PathOriginalStratumTransport Verification.PathOriginalYPresentation
variable (R : Type) [CommRing R] {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)

def ringEquiv : Layer R hI (1:R) 1 ≃+*
    Verification.GlobalNormalFrame.ZeroLayer R Empty n (mutableSet n I) (matrix n) :=
  PathOriginalStratumTransport.equiv hI R R Empty 1 1 isUnit_one isUnit_one (matrix n)
    (presentationEquiv R n).toRingEquiv (presentation_x R n)

def equiv : Layer R hI (1:R) 1 ≃ₐ[R]
    Verification.GlobalNormalFrame.ZeroLayer R Empty n (mutableSet n I) (matrix n) :=
  AlgEquiv.ofRingEquiv (f := ringEquiv R hI) (fun r => by
    have hh := PathOriginalStratumTransport.toOriginal_base hI R R Empty 1 1 isUnit_one isUnit_one
      (matrix n) (presentationEquiv R n).toRingEquiv (presentation_x R n)
      (algebraMap R (Verification.PathPresentation.PathAlgebra n (1:R) 1) r)
    change ringEquiv R hI (algebraMap R (Layer R hI (1:R) 1) r) =
      Verification.OriginalStratumUniversal.baseMap R Empty n (mutableSet n I) (matrix n)
        (presentationEquiv R n (algebraMap R (Verification.PathPresentation.PathAlgebra n (1:R) 1) r)) at hh
    rw [AlgEquiv.commutes,Verification.OriginalStratumUniversal.base_scalar] at hh
    exact hh)

theorem equiv_x (i : Fin n) : equiv R hI (layerX R hI (1:R) 1 i)=
    Verification.OriginalStratumUniversal.baseMap R Empty n (mutableSet n I) (matrix n)
      (Verification.FrozenAcyclicCover.initial R Empty n (matrix n) (Sum.inl i)) :=
  PathOriginalStratumTransport.equiv_x hI R R Empty 1 1 isUnit_one isUnit_one (matrix n)
    (presentationEquiv R n).toRingEquiv (presentation_x R n) i

theorem equiv_y (i : Fin n) : equiv R hI (layerY R hI (1:R) 1 i)=
    Verification.OriginalStratumUniversal.baseMap R Empty n (mutableSet n I) (matrix n)
      (Verification.FrozenAcyclicCover.mutated R Empty n (matrix n) i) := by
  change PathOriginalStratumTransport.toOriginal hI R R Empty 1 1 isUnit_one isUnit_one (matrix n)
    (presentationEquiv R n).toRingEquiv (presentation_x R n)
      (PathStratumRingUniversal.baseMap R hI 1 1 (Verification.PathPresentation.y (1:R) 1 i)) = _
  rw [PathOriginalStratumTransport.toOriginal_base]
  change Verification.OriginalStratumUniversal.baseMap R Empty n (mutableSet n I) (matrix n)
    (presentationEquiv R n (Verification.PathPresentation.y (1:R) 1 i)) = _
  rw [presentation_y]

#print axioms ringEquiv
#print axioms equiv
#print axioms equiv_x
#print axioms equiv_y
end Verification.PathOriginalYStratum
