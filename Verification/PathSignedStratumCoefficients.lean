/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathClassTorus
import Verification.PathLiteralStratum

/-!
# Path Signed Stratum Coefficients

Canonical compressed Laurent coefficients with the two actual endpoint
values imposed. Maps back to the literal localized path retain all signed
original coordinates, including the endpoints.
-/
noncomputable section
namespace Verification.PathSignedStratumCoefficients
open Verification.PathCompression Verification.PathClassRepresentatives
open Verification.OriginalTorus Verification.FinsuppTorusUniversal
open Verification.PathLiteralStratum Verification.PathPresentation
open Finset
variable (R : Type) [CommRing R] {n : ℕ} {I : Finset ℕ} (hI : Admissible n I) (a b : R)

def firstVertex : Vertices n I := includeRepresentative ⟨0,zero_available hI (by omega)⟩
def lastVertex : Vertices n I :=
  ⟨n+1,mem_sdiff.mpr ⟨mem_range.mpr (by omega),by intro hm; have hh:=mem_Icc.mp (hI.1 hm);omega⟩⟩
def endpoint (e : Bool) : Vertices n I := if e then lastVertex hI else firstVertex hI
def endpointValue (e : Bool) : R := if e then (-1)^((n+1)/2)*b else a

def endpointIdeal : Ideal (Torus R (Representatives n I)) :=
  Ideal.span (Set.range (fun e : Bool => torusCoordinate R _ (compress hI (endpoint hI e))-
    algebraMap R _ (endpointValue R (n:=n) a b e)))
abbrev Coefficients := Torus R (Representatives n I) ⧸ endpointIdeal R hI a b

def signedCoordinate (p : Vertices n I) : (Coefficients R hI a b)ˣ :=
  Units.map (Ideal.Quotient.mk (endpointIdeal R hI a b)).toMonoidHom
    (unit R _ (compress hI p))

def unsignedCoordinate (p : Vertices n I) : (Coefficients R hI a b)ˣ :=
  (-1)^(p.val/2)*signedCoordinate R hI a b p

theorem signed_endpoint (e : Bool) :
    (signedCoordinate R hI a b (endpoint hI e) : Coefficients R hI a b)=
      algebraMap R _ (endpointValue R (n:=n) a b e) := by
  apply sub_eq_zero.mp
  change Ideal.Quotient.mk (endpointIdeal R hI a b) (torusCoordinate R _ (compress hI (endpoint hI e)))-
    Ideal.Quotient.mk (endpointIdeal R hI a b) (algebraMap R _ (endpointValue R (n:=n) a b e))=0
  rw [← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self e))

theorem sign_square (p : ℕ) : (-1:R)^p*(-1:R)^p=1 := by
  rw [← mul_pow]
  simp

theorem unsigned_first :
    (unsignedCoordinate R hI a b (firstVertex hI) : Coefficients R hI a b)=algebraMap R _ a := by
  change (-1:Coefficients R hI a b)^(0/2)*
    (signedCoordinate R hI a b (endpoint hI false) : Coefficients R hI a b)=_
  rw [signed_endpoint]
  simp only [Nat.zero_div,pow_zero,one_mul,endpointValue,Bool.false_eq_true,↓reduceIte]

theorem unsigned_last :
    (unsignedCoordinate R hI a b (lastVertex hI) : Coefficients R hI a b)=algebraMap R _ b := by
  change (-1:Coefficients R hI a b)^((n+1)/2)*
    (signedCoordinate R hI a b (endpoint hI true) : Coefficients R hI a b)=_
  rw [signed_endpoint]
  simp only [endpointValue,↓reduceIte,map_mul,map_pow,map_neg,map_one,← mul_assoc,sign_square,one_mul]

theorem unsigned_neighbor (i : I) :
    unsignedCoordinate R hI a b (rightVertex hI i)=-unsignedCoordinate R hI a b (leftVertex hI i) := by
  have he : (i.val+1)/2=(i.val-1)/2+1 := by have hp:=(mem_Icc.mp (hI.1 i.property)).1;omega
  unfold unsignedCoordinate signedCoordinate
  rw [compress_neighbors]
  change (-1:(Coefficients R hI a b)ˣ)^((i.val+1)/2)*_ = -((-1:(Coefficients R hI a b)ˣ)^((i.val-1)/2)*_)
  rw [he,pow_succ]
  apply Units.ext
  simp only [Units.val_mul,Units.val_neg,Units.val_one,Units.val_pow_eq_pow_val]
  ring

def toLayerTorus : Torus R (Representatives n I) →ₐ[R] Layer R hI a b :=
  lift R _ (fun p => signedUnit R hI a b (includeRepresentative p))

theorem toLayerTorus_coordinate (p : Vertices n I) :
    toLayerTorus R hI a b (torusCoordinate R _ (compress hI p))=
      (signedUnit R hI a b p : Layer R hI a b) := by
  rw [toLayerTorus,lift_coordinate]
  exact congrArg Units.val (vertex_evaluate hI (signedUnit R hI a b) (signed_neighbor R hI a b) p)

theorem toLayerTorus_endpoint (e : Bool) :
    toLayerTorus R hI a b (torusCoordinate R _ (compress hI (endpoint hI e)))=
      algebraMap R (Layer R hI a b) (endpointValue R (n:=n) a b e) := by
  rw [toLayerTorus_coordinate,signedUnit_val]
  cases e
  · change (-1:Layer R hI a b)^(0/2)*position R hI a b 0=algebraMap R _ a
    rw [position_boundary,boundary_zero]
    simp
  · change (-1:Layer R hI a b)^((n+1)/2)*position R hI a b (Fin.last (n+1))=
      algebraMap R _ ((-1)^((n+1)/2)*b)
    rw [position_boundary,boundary_last]
    simp only [map_mul,map_pow,map_neg,map_one]

def toLayer : Coefficients R hI a b →ₐ[R] Layer R hI a b :=
  Ideal.Quotient.liftₐ (endpointIdeal R hI a b) (toLayerTorus R hI a b) (by
    change endpointIdeal R hI a b ≤ RingHom.ker (toLayerTorus R hI a b).toRingHom
    apply Ideal.span_le.mpr
    rintro _ ⟨e,rfl⟩
    change toLayerTorus R hI a b (_-_)=0
    rw [map_sub,toLayerTorus_endpoint,AlgHom.commutes,sub_self])

theorem toLayer_signed (p : Vertices n I) :
    toLayer R hI a b (signedCoordinate R hI a b p : Coefficients R hI a b)=
      (signedUnit R hI a b p : Layer R hI a b) :=
  toLayerTorus_coordinate R hI a b p

theorem toLayer_unsigned (p : Vertices n I) :
    toLayer R hI a b (unsignedCoordinate R hI a b p : Coefficients R hI a b)=
      position R hI a b (vertexPosition p) := by
  change toLayer R hI a b ((-1:Coefficients R hI a b)^(p.val/2)*signedCoordinate R hI a b p)=_
  rw [map_mul,map_pow,map_neg,map_one,toLayer_signed,signedUnit_val,← mul_assoc,sign_square,one_mul]

#print axioms firstVertex
#print axioms lastVertex
#print axioms endpoint
#print axioms endpointValue
#print axioms endpointIdeal
#print axioms Coefficients
#print axioms signedCoordinate
#print axioms unsignedCoordinate
#print axioms signed_endpoint
#print axioms sign_square
#print axioms unsigned_first
#print axioms unsigned_last
#print axioms unsigned_neighbor
#print axioms toLayerTorus
#print axioms toLayerTorus_coordinate
#print axioms toLayerTorus_endpoint
#print axioms toLayer
#print axioms toLayer_signed
#print axioms toLayer_unsigned
end Verification.PathSignedStratumCoefficients
