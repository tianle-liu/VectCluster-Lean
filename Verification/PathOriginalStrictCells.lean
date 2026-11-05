/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOriginalFlagIndex
import Verification.PathOriginalAS
import Verification.PathEvenEndpointTorus
import Verification.PathVariableEndpointTorus
import Verification.StrictLocalizedCoordinateTransport

/-!
# Path Original Strict Cells

Actual path strata carry the standard torus--Thom strict cells in
the constructed signed coordinates and increasing original normal frame.
-/
noncomputable section
set_option quotPrecheck false
namespace Verification.PathOriginalStrictCells
open Classical CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.PathCompression Verification.PathOriginalStratumTransport
open Verification.PathOriginalIndependence
universe w₁ w₂
variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w₂} C]
variable {D : Type*} [Category D] [Preadditive D] [HasFiniteBiproducts D]
variable (J : DerivedCategory A ⥤ D) [J.Additive]
variable (L : DerivedCategory C ⥤ D) [L.Additive]
variable (G : Scheme ⥤ CochainComplex C ℤ) (R : Type) [CommRing R]
variable (T : StrictLocalizedCells.TorusCells J L G R)

section Y
variable {d : ℕ} {I : Finset ℕ} (hI : Admissible (2*d) I)
local notation "B" => PathOriginalYPresentation.matrix (2*d)

def yIndex : ActualCellThom.Index Empty (2*d) B I.card :=
  ⟨mutableSet (2*d) I,PathOriginalFlagIndex.mutable_card B y_mutable hI,independent B y_mutable hI⟩

def yBase : GlobalNormalFrame.ZeroLayer R Empty (2*d) (mutableSet (2*d) I) B ≃ₐ[R]
    TorusThomInput.BaseRing R I (PathEvenEndpointTorus.FreeCoordinates hI) :=
  (PathOriginalYStratum.equiv R hI).symm.trans (PathEvenEndpointTorus.stratumEquiv hI R)

variable [Nontrivial R]

def yTerm :
    (StrictLocalizedCells.localCell J L G R T Empty (2*d) B
      (positive_order B y_mutable) (negative_order B y_mutable) (support B y_mutable)
      (fun I hI => (PathOriginalAS.y d I hI).1) (fun I hI => (PathOriginalAS.y d I hI).2)
      I.card (yIndex hI)).term ≅
    (StrictLocalizedCoordinateTransport.standardCell J L G R T I.card I
      (PathEvenEndpointTorus.FreeCoordinates hI)).term :=
  StrictLocalizedCoordinateTransport.termIso J L G R T Empty (2*d) B
    (positive_order B y_mutable) (negative_order B y_mutable) (support B y_mutable)
    (fun I hI => (PathOriginalAS.y d I hI).1) (fun I hI => (PathOriginalAS.y d I hI).2)
    I.card (yIndex hI) I (PathEvenEndpointTorus.FreeCoordinates hI) (yBase R hI)

#print axioms yIndex
#print axioms yBase
#print axioms yTerm
end Y

section Z
variable {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)
local notation "B" => PathOriginalZPresentation.matrix n

def zIndex : ActualCellThom.Index (Fin 1) n B I.card :=
  ⟨mutableSet n I,PathOriginalFlagIndex.mutable_card B z_mutable hI,independent B z_mutable hI⟩

def zBase : GlobalNormalFrame.ZeroLayer R (Fin 1) n (mutableSet n I) B ≃ₐ[R]
    TorusThomInput.BaseRing R I (PathVariableEndpointMaps.FreeCoordinates hI) :=
  (PathOriginalZStratum.equiv R hI).symm.trans (PathVariableEndpointTorus.stratumEquiv R hI)

variable [Nontrivial R]

def zTerm :
    (StrictLocalizedCells.localCell J L G R T (Fin 1) n B
      (positive_order B z_mutable) (negative_order B z_mutable) (support B z_mutable)
      (fun I hI => (PathOriginalAS.z n I hI).1) (fun I hI => (PathOriginalAS.z n I hI).2)
      I.card (zIndex hI)).term ≅
    (StrictLocalizedCoordinateTransport.standardCell J L G R T I.card I
      (PathVariableEndpointMaps.FreeCoordinates hI)).term :=
  StrictLocalizedCoordinateTransport.termIso J L G R T (Fin 1) n B
    (positive_order B z_mutable) (negative_order B z_mutable) (support B z_mutable)
    (fun I hI => (PathOriginalAS.z n I hI).1) (fun I hI => (PathOriginalAS.z n I hI).2)
    I.card (zIndex hI) I (PathVariableEndpointMaps.FreeCoordinates hI) (zBase R hI)

#print axioms zIndex
#print axioms zBase
#print axioms zTerm
end Z
end Verification.PathOriginalStrictCells
