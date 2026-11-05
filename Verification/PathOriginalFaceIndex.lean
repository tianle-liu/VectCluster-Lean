/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathOriginalIndependence
import Verification.PathSignedFaceUnits

/-!
# Path Original Face Index

The normal vertex and its incidence count in the actual global flag
are the original positive path vertex and its preceding selected vertices.
-/
namespace Verification.PathOriginalFaceIndex
open Finset Verification.PathCompression Verification.PathOriginalStratumTransport
open Verification.IndependentChartIndex
variable {n : ℕ} {I : Finset ℕ}
variable (j : ℕ) (hj : j∈Icc 1 n)

def normal : Fin n := ⟨j-1,by have h:=mem_Icc.mp hj;omega⟩

theorem normal_position : (normal j hj).val+1=j := by
  have h:=mem_Icc.mp hj
  dsimp [normal]
  omega

theorem mutable_insert : mutableSet n (insert j I)=insert (normal j hj) (mutableSet n I) := by
  ext i
  have h:=mem_Icc.mp hj
  have he : i.val+1=j ↔ i.val=j-1 := by omega
  simpa only [mem_mutableSet,mem_insert,Fin.ext_iff,normal] using
    (or_congr he (Iff.refl (i.val+1∈I)))

theorem normal_not_mem (ha : Addable I j) : normal j hj∉mutableSet n I := by
  rw [mem_mutableSet,normal_position]
  intro h
  exact ha.1 (mem_union.mpr (Or.inl h))

theorem mutable_erase (ha : Addable I j) : (mutableSet n (insert j I)).erase (normal j hj)=mutableSet n I := by
  rw [mutable_insert,erase_insert (normal_not_mem j hj ha)]

def selectedNormal : Selected n (mutableSet n (insert j I)) :=
  ⟨normal j hj,by rw [mutable_insert];exact mem_insert_self _ _⟩

variable (hI : Admissible n I)

include hI in
theorem preceding_count :
    (((univ.erase (selectedNormal (I:=I) j hj)).filter
      (fun i : Selected n (mutableSet n (insert j I)) => i<selectedNormal j hj))).card=
      (I.filter (fun k => k<j)).card := by
  apply card_bij (fun i _ => i.val.val+1)
  · intro i hi
    rcases mem_filter.mp hi with ⟨_,hi⟩
    have hm := (mem_mutableSet n (insert j I) i.val).mp i.property
    have hl : i.val.val<j-1 := hi
    have hle:=mem_Icc.mp hj
    exact mem_filter.mpr ⟨(mem_insert.mp hm).resolve_left (by omega),by omega⟩
  · intro a _ b _ h
    apply Subtype.ext
    apply Fin.ext
    omega
  · intro k hk
    rcases mem_filter.mp hk with ⟨hk,hl⟩
    have hb:=mem_Icc.mp (hI.1 hk)
    let a : Selected n (mutableSet n (insert j I)) :=
      ⟨⟨k-1,by omega⟩,by rw [mem_mutableSet];exact mem_insert_of_mem (by simpa only [Nat.sub_add_cancel hb.1] using hk)⟩
    refine ⟨a,mem_filter.mpr ⟨mem_erase.mpr ⟨?_,mem_univ _⟩,?_⟩,?_⟩
    · intro he
      have hh:=congrArg (fun i : Selected n (mutableSet n (insert j I)) => i.val.val) he
      dsimp [a,selectedNormal,normal] at hh
      omega
    · change k-1<j-1
      omega
    · dsimp [a]
      omega

#print axioms normal
#print axioms normal_position
#print axioms mutable_insert
#print axioms normal_not_mem
#print axioms mutable_erase
#print axioms selectedNormal
#print axioms preceding_count
end Verification.PathOriginalFaceIndex
