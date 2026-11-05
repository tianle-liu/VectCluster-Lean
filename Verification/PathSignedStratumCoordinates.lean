/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathSignedStratumCoefficients
import Verification.PathLiteralStratumUniversal

/-!
# Path Signed Stratum Coordinates

Actual nearest-neighbor coordinate and partner formulas in the compressed
Laurent coefficient algebra, with one free partner for each zero vertex.
-/
noncomputable section
namespace Verification.PathSignedStratumCoordinates
open Verification.PathCompression Verification.PathClassRepresentatives
open Verification.PathLiteralStratum Verification.PathSignedStratumCoefficients
open Verification.PathPresentation MvPolynomial Finset
variable (R : Type) [CommRing R] {n : ℕ} {I : Finset ℕ} (hI : Admissible n I) (a b : R)

def coordinate (p : Fin (n+2)) : Coefficients R hI a b :=
  if hp : p.val ∈ I then 0 else unsignedCoordinate R hI a b
    ⟨p.val,mem_sdiff.mpr ⟨mem_range.mpr p.isLt,hp⟩⟩

theorem coordinate_zero (p : Fin (n+2)) (hp : p.val ∈ I) : coordinate R hI a b p=0 := by
  simp only [coordinate,dif_pos hp]

theorem coordinate_vertex (p : Vertices n I) :
    coordinate R hI a b (vertexPosition p)=(unsignedCoordinate R hI a b p : Coefficients R hI a b) := by
  dsimp only [coordinate,vertexPosition]
  rw [dif_neg (mem_sdiff.mp p.property).2]
  rfl

theorem coordinate_first : coordinate R hI a b 0=algebraMap R _ a := by
  change coordinate R hI a b (vertexPosition (firstVertex hI))=_
  rw [coordinate_vertex,unsigned_first]

theorem coordinate_last : coordinate R hI a b (Fin.last (n+1))=algebraMap R _ b := by
  change coordinate R hI a b (vertexPosition (lastVertex hI))=_
  rw [coordinate_vertex,unsigned_last]

theorem coordinate_boundary (p : Fin (n+2)) : coordinate R hI a b p=
    boundary (algebraMap R _ a) (algebraMap R _ b) (fun i => coordinate R hI a b i.castSucc.succ) p := by
  induction p using Fin.cases with
  | zero => rw [boundary_zero,coordinate_first]
  | succ p =>
    induction p using Fin.lastCases with
    | last => exact (coordinate_last R hI a b).trans (boundary_last _ _ _).symm
    | cast p => rw [boundary_middle]

theorem coordinate_neighbors (i : I) :
    coordinate R hI a b (mutableIndex hI i).castSucc.castSucc+
      coordinate R hI a b (mutableIndex hI i).succ.succ=0 := by
  rw [← position_left,← position_right,coordinate_vertex,coordinate_vertex,unsigned_neighbor,Units.val_neg,add_neg_cancel]

abbrev Target := MvPolynomial I (Coefficients R hI a b)

def targetX (i : Fin n) : Target R hI a b := C (coordinate R hI a b i.castSucc.succ)

def nonzeroVertex (i : Fin n) (hi : i.val+1 ∉ I) : Vertices n I :=
  ⟨i.val+1,mem_sdiff.mpr ⟨mem_range.mpr (by omega),hi⟩⟩

def targetY (i : Fin n) : Target R hI a b :=
  if hi : i.val+1 ∈ I then X ⟨i.val+1,hi⟩ else
    C (((unsignedCoordinate R hI a b (nonzeroVertex i hi))⁻¹ : (Coefficients R hI a b)ˣ)*
      (coordinate R hI a b i.castSucc.castSucc+coordinate R hI a b i.succ.succ))

theorem target_boundary (p : Fin (n+2)) :
    boundary (algebraMap R (Target R hI a b) a) (algebraMap R _ b) (targetX R hI a b) p=
      C (coordinate R hI a b p) := by
  rw [coordinate_boundary R hI a b p,boundary_map C]
  rfl

theorem mutable_position (i : I) : (mutableIndex hI i).val+1=i.val := by
  have hp := (mem_Icc.mp (hI.1 i.property)).1
  dsimp [mutableIndex]
  omega

theorem target_zero (i : I) : targetX R hI a b (mutableIndex hI i)=0 := by
  rw [targetX,coordinate_zero,map_zero]
  change (mutableIndex hI i).val+1 ∈ I
  rw [mutable_position]
  exact i.property

theorem target_equations : Equations (algebraMap R (Target R hI a b) a)
    (algebraMap R _ b) (targetX R hI a b) (targetY R hI a b) := by
  intro i
  rw [target_boundary,target_boundary,← map_add]
  by_cases hi : i.val+1 ∈ I
  · let j : I := ⟨i.val+1,hi⟩
    have hj : mutableIndex hI j=i := by apply Fin.ext; dsimp [mutableIndex,j]
    rw [← hj,target_zero,zero_mul,coordinate_neighbors,map_zero]
  · rw [targetY,dif_neg hi,targetX]
    have hc : coordinate R hI a b i.castSucc.succ=
        (unsignedCoordinate R hI a b (nonzeroVertex i hi) : Coefficients R hI a b) :=
      coordinate_vertex R hI a b (nonzeroVertex i hi)
    rw [hc,← map_mul,← mul_assoc,Units.mul_inv,one_mul]

theorem target_units (p : Vertices n I) :
    IsUnit (boundary (algebraMap R (Target R hI a b) a) (algebraMap R _ b) (targetX R hI a b) (vertexPosition p)) := by
  rw [target_boundary,coordinate_vertex]
  exact (unsignedCoordinate R hI a b p).isUnit.map C

theorem target_selected_partner (i : I) : targetY R hI a b (mutableIndex hI i)=X i := by
  rw [targetY]
  have hi : (mutableIndex hI i).val+1 ∈ I := by rw [mutable_position];exact i.property
  rw [dif_pos hi]
  congr 1
  apply Subtype.ext
  exact mutable_position hI i

#print axioms coordinate
#print axioms coordinate_zero
#print axioms coordinate_vertex
#print axioms coordinate_first
#print axioms coordinate_last
#print axioms coordinate_boundary
#print axioms coordinate_neighbors
#print axioms Target
#print axioms targetX
#print axioms nonzeroVertex
#print axioms targetY
#print axioms target_boundary
#print axioms mutable_position
#print axioms target_zero
#print axioms target_equations
#print axioms target_units
#print axioms target_selected_partner
end Verification.PathSignedStratumCoordinates
