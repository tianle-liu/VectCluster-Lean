/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOriginalAS
import Verification.PathOriginalZEquivalence

/-!
# Path Minimal Smooth

Smoothness of the literal minimal Y and Z path algebras follows from
their proved AS matrices and their actual original-presentation equivalences.
-/
noncomputable section
namespace Verification.PathMinimalSmooth
open Verification.PathOriginalIndependence
variable (R : Type) [CommRing R] [Nontrivial R]

def y (d : ℕ) : Algebra.Smooth R (PathPresentation.PathAlgebra (2*d) (1:R) 1) := by
  let B := PathOriginalYPresentation.matrix (2*d)
  letI := GlobalExchangeSmooth.global_smooth_saturated R Empty (2*d) B
    (positive_order B y_mutable) (negative_order B y_mutable) (support B y_mutable)
    (fun I hI=>(PathOriginalAS.y d I hI).1) (fun I hI=>(PathOriginalAS.y d I hI).2)
  exact Algebra.Smooth.of_equiv (PathOriginalYPresentation.presentationEquiv R (2*d)).symm

def z (n : ℕ) : Algebra.Smooth R (PathOriginalZPresentation.Path R n) := by
  let B := PathOriginalZPresentation.matrix n
  letI := GlobalExchangeSmooth.global_smooth_saturated R (Fin 1) n B
    (positive_order B z_mutable) (negative_order B z_mutable) (support B z_mutable)
    (fun I hI=>(PathOriginalAS.z n I hI).1) (fun I hI=>(PathOriginalAS.z n I hI).2)
  exact Algebra.Smooth.of_equiv (PathOriginalZEquivalence.equiv R n).symm

#print axioms y
#print axioms z
end Verification.PathMinimalSmooth
