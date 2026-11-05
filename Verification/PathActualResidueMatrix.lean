/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathActualResidueCoordinates

/-!
# Path Actual Residue Matrix

Matrix multiplication for the genuine actual path face residue on
arbitrary section vectors, deduced from its computed basis columns.
-/
noncomputable section
set_option quotPrecheck false
namespace Verification.PathActualResidueMatrix
open Classical CategoryTheory AlgebraicGeometry
open Verification.PathCompression Verification.PathSignedFaceUnits
open Verification.PathActualWordIndices Verification.PathMilnorWittCoefficients
open Verification.PathActualResidueCoordinates

section Y
variable (R : Type) [CommRing R] {d : ℕ} {I : Finset ℕ} (hI : Admissible (2*d) I)
variable (j : ℕ) (hj : j∈Finset.Icc 1 (2*d)) (ha : Addable I j)
variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (D : GradedMilnorWittSheaf.Standard site N)
variable (K : StandardThomContractionNormalization.Grading R site N)
variable (P : GradedMilnorWittLaurent.Standard R site N D K)
local notation "SI" => BinaryWordCoordinates.Index (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI))
local notation "TI" => BinaryWordCoordinates.Index (Fintype.card (PathEvenEndpointTorus.FreeCoordinates (nextAdmissible hI j hj ha)))
local notation "DR" => D.symbols (CommRingCat.of R)
include P

theorem y_apply (f : SI → D.Total (CommRingCat.of R)) (k : TI) :
    yFace R hI j hj ha site N D K f k=
      ∑ i:SI,((DR).g^(j/2)*realize (DR).toCoefficients
        (yColumn hI j i (yWordEquiv (nextAdmissible hI j hj ha) k).val))*f i := by
  have hf : f=∑ i:SI,Pi.single i (f i) := by
    funext i
    simp [Pi.single_apply,eq_comm]
  conv_lhs => rw [hf]
  rw [map_sum,Finset.sum_apply]
  exact Finset.sum_congr rfl (fun i _ => yFace_single R hI j hj ha site N D K P i (f i) k)
end Y

section Z
variable (R : Type) [CommRing R] {n : ℕ} {I : Finset ℕ} (hI : Admissible (n) I)
variable (j : ℕ) (hj : j∈Finset.Icc 1 (n)) (ha : Addable I j)
variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (D : GradedMilnorWittSheaf.Standard site N)
variable (K : StandardThomContractionNormalization.Grading R site N)
variable (P : GradedMilnorWittLaurent.Standard R site N D K)
local notation "SI" => BinaryWordCoordinates.Index (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI))
local notation "TI" => BinaryWordCoordinates.Index (Fintype.card (PathVariableEndpointMaps.FreeCoordinates (nextAdmissible hI j hj ha)))
local notation "DR" => D.symbols (CommRingCat.of R)
include P

theorem z_apply (f : SI → D.Total (CommRingCat.of R)) (k : TI) :
    zFace R hI j hj ha site N D K f k=
      ∑ i:SI,((DR).g^(j/2)*realize (DR).toCoefficients
        (zColumn hI j i (zWordEquiv (nextAdmissible hI j hj ha) k).val))*f i := by
  have hf : f=∑ i:SI,Pi.single i (f i) := by
    funext i
    simp [Pi.single_apply,eq_comm]
  conv_lhs => rw [hf]
  rw [map_sum,Finset.sum_apply]
  exact Finset.sum_congr rfl (fun i _ => zFace_single R hI j hj ha site N D K P i (f i) k)
end Z

#print axioms y_apply
#print axioms z_apply
end Verification.PathActualResidueMatrix
