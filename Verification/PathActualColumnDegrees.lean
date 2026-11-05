/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathActualResidueCoordinates
import Verification.PathMatrixCoefficientGrading
import Verification.StrictTorusSymbolInput

/-!
# Path Actual Column Degrees

The degrees of the genuine signed path word columns agree with the ordinary strict summand degrees.
-/
noncomputable section
namespace Verification.PathActualColumnDegrees
open Classical Verification.PathCompression Verification.PathSignedFaceUnits
open Verification.PathActualWordIndices Verification.BinaryWordCoordinates
open Verification.PathCoefficientRing Verification.PathCoefficientGrading

theorem count_toList (n : ℕ) (i : Index n) :
    ((Verification.BinaryPathWordEquiv.toList n i).count true : ℤ)=
      Verification.GradedBinaryCoefficientTree.weight n i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases i with ⟨b,i⟩
    cases b <;> simp [Verification.BinaryPathWordEquiv.toList,Verification.GradedBinaryCoefficientTree.weight,ih,add_comm]

section Y
variable {d : ℕ} {I : Finset ℕ} (hI : Admissible (2*d) I)
local notation "SI" => Index (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI))

theorem y_count (i : SI) :
    (((yWordEquiv hI i).val).count true : ℤ)=
      Verification.GradedBinaryCoefficientTree.weight (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI)) i := by
  simpa [yWordEquiv_val] using count_toList (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI)) i

variable (j : ℕ) (hj : j∈Finset.Icc 1 (2*d)) (ha : Addable I j)
local notation "hJ" => nextAdmissible hI j hj ha
local notation "TI" => Index (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hJ))

def yEntry (i : SI) (k : TI) : Coeff :=
  g^(PathRhoConfiguration.rank I j)*(g^(j/2)*
    PathActualResidueCoordinates.yColumn hI j i (yWordEquiv hJ k).val)

theorem y_column_degree (i : SI) (k : TI) :
    Homogeneous
      (StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI)) i-
        StrictTorusSymbolInput.degree (Fintype.card (Fin (I.card+1))) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hJ)) k)
      (PathActualResidueCoordinates.yColumn hI j i (yWordEquiv hJ k).val) := by
  obtain ⟨c,v,hc,hdeg⟩ := PathMatrixCoefficientGrading.both_column d
    (faceIndex I j) (yWordEquiv hI i).val
  change Homogeneous _ ((PathLeftEndpoint.projection 0 (PathLiteralEntries.projectedFace g rho (2*d) (faceIndex I j)
    (yWordEquiv hI i).val)) (yWordEquiv hJ k).val)
  rw [hc]
  have hsingle := PathMatrixCoefficientGrading.single_degree (((yWordEquiv hI i).val.count true : ℤ)-1)
    c v (yWordEquiv hJ k).val (by convert hdeg using 1; omega)
  convert hsingle using 1
  rw [y_count,y_count]
  simp only [StrictTorusSymbolInput.degree,Fintype.card_fin,Nat.cast_add,Nat.cast_one]
  omega

theorem y_entry_degree (i : SI) (k : TI) :
    Homogeneous
      (StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hI)) i-
        StrictTorusSymbolInput.degree (Fintype.card (Fin (I.card+1))) (Fintype.card (PathEvenEndpointTorus.FreeCoordinates hJ)) k)
      (yEntry hI j hj ha i k) := by
  have hp (a : ℕ) : Homogeneous 0 (g^a) := by
    simpa only [mul_zero] using PathMatrixCoefficientGrading.power g 0 homogeneous_g a
  simpa only [zero_add] using homogeneous_mul (hp (PathRhoConfiguration.rank I j))
    (homogeneous_mul (hp (j/2)) (y_column_degree hI j hj ha i k))

#print axioms y_count
#print axioms yEntry
#print axioms y_column_degree
#print axioms y_entry_degree
end Y

section Z
variable {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)
local notation "SI" => Index (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI))

theorem z_count (i : SI) :
    (((zWordEquiv hI i).val).count true : ℤ)=
      Verification.GradedBinaryCoefficientTree.weight (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI)) i := by
  simpa [zWordEquiv_val] using count_toList (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI)) i

variable (j : ℕ) (hj : j∈Finset.Icc 1 n) (ha : Addable I j)
local notation "hJ" => nextAdmissible hI j hj ha
local notation "TI" => Index (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hJ))

def zEntry (i : SI) (k : TI) : Coeff :=
  g^(PathRhoConfiguration.rank I j)*(g^(j/2)*
    PathActualResidueCoordinates.zColumn hI j i (zWordEquiv hJ k).val)

theorem z_column_degree (i : SI) (k : TI) :
    Homogeneous
      (StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI)) i-
        StrictTorusSymbolInput.degree (Fintype.card (Fin (I.card+1))) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hJ)) k)
      (PathActualResidueCoordinates.zColumn hI j i (zWordEquiv hJ k).val) := by
  obtain ⟨c,v,hc,hdeg⟩ := PathMatrixCoefficientGrading.projected_column n
    (faceIndex I j) (zWordEquiv hI i).val
  change Homogeneous _ ((PathLiteralEntries.projectedFace g rho n (faceIndex I j)
    (zWordEquiv hI i).val) (zWordEquiv hJ k).val)
  rw [hc]
  have hsingle := PathMatrixCoefficientGrading.single_degree (((zWordEquiv hI i).val.count true : ℤ)-1)
    c v (zWordEquiv hJ k).val (by convert hdeg using 1; omega)
  convert hsingle using 1
  rw [z_count,z_count]
  simp only [StrictTorusSymbolInput.degree,Fintype.card_fin,Nat.cast_add,Nat.cast_one]
  omega

theorem z_entry_degree (i : SI) (k : TI) :
    Homogeneous
      (StrictTorusSymbolInput.degree (Fintype.card (Fin I.card)) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hI)) i-
        StrictTorusSymbolInput.degree (Fintype.card (Fin (I.card+1))) (Fintype.card (PathVariableEndpointMaps.FreeCoordinates hJ)) k)
      (zEntry hI j hj ha i k) := by
  have hp (a : ℕ) : Homogeneous 0 (g^a) := by
    simpa only [mul_zero] using PathMatrixCoefficientGrading.power g 0 homogeneous_g a
  simpa only [zero_add] using homogeneous_mul (hp (PathRhoConfiguration.rank I j))
    (homogeneous_mul (hp (j/2)) (z_column_degree hI j hj ha i k))

#print axioms z_count
#print axioms zEntry
#print axioms z_column_degree
#print axioms z_entry_degree
end Z

#print axioms count_toList
end Verification.PathActualColumnDegrees
