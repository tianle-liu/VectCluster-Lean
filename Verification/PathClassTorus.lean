/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathClassRepresentatives
import Verification.FinsuppTorusUniversal

/-!
# Path Class Torus

The signed path neighbor relations give an explicit Laurent algebra on
exactly the canonical surviving classes, with both endpoints still present.
-/
noncomputable section
namespace Verification.PathClassTorus
open Verification.PathCompression Verification.PathClassRepresentatives
open Verification.OriginalTorus Verification.FinsuppTorusUniversal
variable (R : Type) [CommRing R] {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)

def relations : Ideal (Torus R (Vertices n I)) :=
  Ideal.span (Set.range (fun i : I => torusCoordinate R _ (rightVertex hI i)-
    torusCoordinate R _ (leftVertex hI i)))
abbrev Quotient := Torus R (Vertices n I) ⧸ relations R hI

def coordinate (p : Vertices n I) : Quotient R hI :=
  Ideal.Quotient.mk (relations R hI) (torusCoordinate R _ p)

def coordinateUnit (p : Vertices n I) : (Quotient R hI)ˣ :=
  Units.map (Ideal.Quotient.mk (relations R hI)).toMonoidHom (unit R _ p)

theorem coordinateUnit_val (p : Vertices n I) :
    (coordinateUnit R hI p : Quotient R hI)=coordinate R hI p := rfl

theorem neighbor_relation (i : I) :
    coordinate R hI (rightVertex hI i)=coordinate R hI (leftVertex hI i) := by
  apply sub_eq_zero.mp
  change Ideal.Quotient.mk (relations R hI) (torusCoordinate R _ (rightVertex hI i))-
    Ideal.Quotient.mk (relations R hI) (torusCoordinate R _ (leftVertex hI i))=0
  rw [← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))

def forward : Quotient R hI →ₐ[R] Torus R (Representatives n I) :=
  Ideal.Quotient.liftₐ (relations R hI)
    (lift R _ (fun p => unit R _ (compress hI p))) (by
      change relations R hI ≤ RingHom.ker (lift R _ (fun p => unit R _ (compress hI p))).toRingHom
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      change lift R _ _ (torusCoordinate R _ (rightVertex hI i)-
        torusCoordinate R _ (leftVertex hI i))=0
      rw [map_sub,lift_coordinate,lift_coordinate,compress_neighbors,sub_self])

theorem forward_coordinate (p : Vertices n I) :
    forward R hI (coordinate R hI p)=torusCoordinate R _ (compress hI p) :=
  lift_coordinate R _ _ p

def backward : Torus R (Representatives n I) →ₐ[R] Quotient R hI :=
  lift R _ (fun p => coordinateUnit R hI (includeRepresentative p))

theorem backward_coordinate (p : Representatives n I) :
    backward R hI (torusCoordinate R _ p)=coordinate R hI (includeRepresentative p) :=
  lift_coordinate R _ _ p

theorem forward_backward : (forward R hI).comp (backward R hI)=AlgHom.id R _ := by
  apply FinsuppTorusUniversal.hom_ext
  intro p
  change forward R hI (backward R hI (torusCoordinate R _ p))=torusCoordinate R _ p
  rw [backward_coordinate,forward_coordinate,compress_include]

theorem backward_forward : (backward R hI).comp (forward R hI)=AlgHom.id R _ := by
  apply Ideal.Quotient.algHom_ext
  apply FinsuppTorusUniversal.hom_ext
  intro p
  change backward R hI (forward R hI (coordinate R hI p))=coordinate R hI p
  rw [forward_coordinate,backward_coordinate]
  exact vertex_evaluate hI (coordinate R hI) (neighbor_relation R hI) p

def compressionEquiv : Quotient R hI ≃ₐ[R] Torus R (Representatives n I) :=
  AlgEquiv.ofAlgHom (forward R hI) (backward R hI)
    (forward_backward R hI) (backward_forward R hI)

theorem compression_coordinate (p : Vertices n I) :
    compressionEquiv R hI (coordinate R hI p)=torusCoordinate R _ (compress hI p) :=
  forward_coordinate R hI p

theorem compression_inverse_coordinate (p : Representatives n I) :
    (compressionEquiv R hI).symm (torusCoordinate R _ p)=coordinate R hI (includeRepresentative p) :=
  backward_coordinate R hI p

#print axioms relations
#print axioms Quotient
#print axioms coordinate
#print axioms coordinateUnit
#print axioms coordinateUnit_val
#print axioms neighbor_relation
#print axioms forward
#print axioms forward_coordinate
#print axioms backward
#print axioms backward_coordinate
#print axioms forward_backward
#print axioms backward_forward
#print axioms compressionEquiv
#print axioms compression_coordinate
#print axioms compression_inverse_coordinate
end Verification.PathClassTorus
