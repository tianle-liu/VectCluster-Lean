/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathFreeCoordinateOrder
import Verification.BinaryPathWordEquiv

/-!
# Path Actual Word Indices

Bijections from actual Laurent word bases to the literal normal-word
indices of the endpoint path complexes, retaining their zero-set degree.
-/
noncomputable section
namespace Verification.PathActualWordIndices
open Classical Verification.PathCompression Verification.PathCochains
open Verification.PathNormalizedBasis Verification.PathEndpointWords
open Verification.BinaryWordCoordinates Verification.PathFreeCoordinateOrder

def normalCast (B : List Bool → Prop) {m n : ℕ} (h : m=n) : NormalWord B m ≃ NormalWord B n where
  toFun w := ⟨w.val,by simpa only [← h] using w.property⟩
  invFun w := ⟨w.val,by simpa only [h] using w.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem normalCast_val (B : List Bool → Prop) {m n : ℕ} (h : m=n) (w : NormalWord B m) :
    (normalCast B h w).val=w.val := rfl

variable {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)
local notation "Z" => PathVariableEndpointMaps.FreeCoordinates hI

def zWordEquiv : Index (Fintype.card Z) ≃ NormalWord RightNormal (available I (n+2)).card :=
  (BinaryPathWordEquiv.rightEquiv (Fintype.card Z)).trans (normalCast RightNormal (z_card hI))

theorem zWordEquiv_val (i : Index (Fintype.card Z)) :
    (zWordEquiv hI i).val=BinaryPathWordEquiv.toList (Fintype.card Z) i++[false] := rfl

variable {a : ℕ} (hY : Admissible (2*a) I)
local notation "Y" => PathEvenEndpointTorus.FreeCoordinates hY

def yWordEquiv : Index (Fintype.card Y) ≃ NormalWord BothNormal (available I (2*a+2)).card :=
  (BinaryPathWordEquiv.bothEquiv (Fintype.card Y)).trans (normalCast BothNormal (y_card hY))

theorem yWordEquiv_val (i : Index (Fintype.card Y)) :
    (yWordEquiv hY i).val=false::(BinaryPathWordEquiv.toList (Fintype.card Y) i++[false]) := rfl

def zIndexEquiv (n : ℕ) :
    (Σ I : Config n, Index (Fintype.card (PathVariableEndpointMaps.FreeCoordinates I.property))) ≃
      NormalIndex RightNormal n := Equiv.sigmaCongrRight (fun I => zWordEquiv I.property)

def yIndexEquiv (a : ℕ) :
    (Σ I : Config (2*a), Index (Fintype.card (PathEvenEndpointTorus.FreeCoordinates I.property))) ≃
      NormalIndex BothNormal (2*a) := Equiv.sigmaCongrRight (fun I => yWordEquiv I.property)

theorem zIndex_degree (n : ℕ)
    (i : Σ I : Config n, Index (Fintype.card (PathVariableEndpointMaps.FreeCoordinates I.property))) :
    ((zIndexEquiv n i).1).val.card=i.1.val.card := rfl

theorem yIndex_degree (a : ℕ)
    (i : Σ I : Config (2*a), Index (Fintype.card (PathEvenEndpointTorus.FreeCoordinates I.property))) :
    ((yIndexEquiv a i).1).val.card=i.1.val.card := rfl

#print axioms normalCast
#print axioms normalCast_val
#print axioms zWordEquiv
#print axioms zWordEquiv_val
#print axioms yWordEquiv
#print axioms yWordEquiv_val
#print axioms zIndexEquiv
#print axioms yIndexEquiv
#print axioms zIndex_degree
#print axioms yIndex_degree
end Verification.PathActualWordIndices
