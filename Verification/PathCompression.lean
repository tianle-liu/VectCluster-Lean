/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Tauto
import Lean.Elab.Tactic.Omega

/-!
# Path Compression

The actual coordinate compression determined by independent zero vertices.
Vertices are 0,...,n+1; endpoints are not zero vertices. Imposing zero at i
removes i and the right copy i+1, merging its neighbors into the left class.
The proofs identify the exact shifts needed by the rho face operators.
-/

namespace Verification.PathCompression

open Finset

/-- Mutable zero sets of the literal path, with both outer positions retained. -/
def Admissible (n : ℕ) (I : Finset ℕ) : Prop :=
  I ⊆ Icc 1 n ∧ ∀ i ∈ I, i+1 ∉ I

def deleted (I : Finset ℕ) : Finset ℕ := I ∪ I.image Nat.succ

def available (I : Finset ℕ) (N : ℕ) : Finset ℕ := range N \ deleted I

def coordinate (I : Finset ℕ) (j : ℕ) : ℕ := (available I j).card

def Addable (I : Finset ℕ) (j : ℕ) : Prop := j ∉ deleted I ∧ j+1 ∉ deleted I

def faceIndex (I : Finset ℕ) (j : ℕ) : ℕ := coordinate I j-1

theorem deleted_insert (I : Finset ℕ) (i : ℕ) :
    deleted (insert i I)=insert (i+1) (insert i (deleted I)) := by
  ext k
  simp only [deleted,mem_union,mem_insert,image_insert]
  tauto

theorem available_insert (I : Finset ℕ) (i N : ℕ) :
    available (insert i I) N=((available I N).erase i).erase (i+1) := by
  ext k
  simp only [available,deleted_insert,mem_sdiff,mem_insert,mem_erase]
  tauto

theorem available_mono (I : Finset ℕ) {N M : ℕ} (h : N ≤ M) :
    available I N ⊆ available I M := by
  intro k hk
  rcases mem_sdiff.mp hk with ⟨hk,hd⟩
  exact mem_sdiff.mpr ⟨mem_range.mpr (by have hh:=mem_range.mp hk; omega),hd⟩

theorem available_insert_card (I : Finset ℕ) (i N : ℕ) (hi : Addable I i) (hN : i+1<N) :
    (available (insert i I) N).card+2=(available I N).card := by
  have hm : i ∈ available I N := mem_sdiff.mpr ⟨mem_range.mpr (by omega),hi.1⟩
  have hm' : i+1 ∈ (available I N).erase i :=
    mem_erase.mpr ⟨by omega,mem_sdiff.mpr ⟨mem_range.mpr hN,hi.2⟩⟩
  have h₁ := card_erase_add_one hm
  have h₂ := card_erase_add_one hm'
  rw [available_insert]
  omega

theorem coordinate_insert_after (I : Finset ℕ) (i j : ℕ) (hi : Addable I i) (hij : i+2 ≤ j) :
    coordinate (insert i I) j+2=coordinate I j :=
  available_insert_card I i j hi (by omega)

theorem coordinate_insert_before (I : Finset ℕ) (i j : ℕ) (hji : j ≤ i) :
    coordinate (insert i I) j=coordinate I j := by
  unfold coordinate
  rw [available_insert]
  have h₁ : i ∉ available I j := by
    intro hm
    have hh := mem_range.mp (mem_sdiff.mp hm).1
    omega
  have h₂ : i+1 ∉ available I j := by
    intro hm
    have hh := mem_range.mp (mem_sdiff.mp hm).1
    omega
  rw [erase_eq_of_not_mem h₁,erase_eq_of_not_mem h₂]

/-- The two surviving positions i and i+1 certify separation after compression. -/
theorem coordinate_separated (I : Finset ℕ) (i j : ℕ) (hi : Addable I i) (hij : i+2 ≤ j) :
    coordinate I i+2 ≤ coordinate I j := by
  have hsub : insert (i+1) (insert i (available I i)) ⊆ available I j := by
    intro k hk
    rcases mem_insert.mp hk with rfl | hk
    · exact mem_sdiff.mpr ⟨mem_range.mpr (by omega),hi.2⟩
    rcases mem_insert.mp hk with rfl | hk
    · exact mem_sdiff.mpr ⟨mem_range.mpr (by omega),hi.1⟩
    · exact available_mono I (by omega) hk
  have h₁ : i ∉ available I i := by simp [available]
  have h₂ : i+1 ∉ insert i (available I i) := by simp [available]
  have hh := card_le_card hsub
  rw [card_insert_of_not_mem h₂,card_insert_of_not_mem h₁] at hh
  exact hh

theorem zero_available {n : ℕ} {I : Finset ℕ} (hI : Admissible n I) {N : ℕ} (hN : 0<N) :
    0 ∈ available I N := by
  refine mem_sdiff.mpr ⟨mem_range.mpr hN,?_⟩
  simp only [deleted,mem_union,mem_image,not_or,not_exists]
  constructor
  · intro h
    have hh := mem_Icc.mp (hI.1 h)
    omega
  · intro k h
    have hh := h.2
    omega

theorem coordinate_positive {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)
    {j : ℕ} (hj : 0<j) : 0<coordinate I j :=
  card_pos.mpr ⟨0,zero_available hI hj⟩

/-- The left-neighbor index used by the literal word face shifts by exactly two. -/
theorem faceIndex_insert_after (I : Finset ℕ) (i j : ℕ) (hi : Addable I i) (hij : i+2 ≤ j) :
    faceIndex (insert i I) j=faceIndex I j-2 := by
  have hh := coordinate_insert_after I i j hi hij
  unfold faceIndex
  omega

theorem faceIndex_insert_before (I : Finset ℕ) (i j : ℕ) (hji : j ≤ i) :
    faceIndex (insert i I) j=faceIndex I j := by
  unfold faceIndex
  rw [coordinate_insert_before I i j hji]

theorem faceIndex_separated (I : Finset ℕ) (i j : ℕ) (hi : Addable I i) (hij : i+2 ≤ j)
    (hpos : 0<coordinate I i) : faceIndex I i+2 ≤ faceIndex I j := by
  have hh := coordinate_separated I i j hi hij
  unfold faceIndex
  omega

theorem faceIndex_valid {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)
    (j : ℕ) (hj : j ∈ Icc 1 n) (ha : Addable I j) :
    faceIndex I j+3 ≤ (available I (n+2)).card := by
  have hp := coordinate_positive hI (by have hh:=mem_Icc.mp hj; omega : 0<j)
  have hh := coordinate_separated I j (n+2) ha (by have hh:=mem_Icc.mp hj; omega)
  unfold faceIndex coordinate at *
  omega

theorem admissible_pair {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)
    {i j : ℕ} (hi : i ∈ I) (hj : j ∈ I) (hij : i<j) : i+2 ≤ j := by
  have hh := hI.2 i hi
  by_contra h
  have he : j=i+1 := by omega
  exact hh (he ▸ hj)

theorem admissible_insert {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)
    (i : ℕ) (hi : i ∈ Icc 1 n) (ha : Addable I i) : Admissible n (insert i I) := by
  constructor
  · exact insert_subset hi hI.1
  · intro k hk
    rcases mem_insert.mp hk with rfl | hk
    · intro hm
      rcases mem_insert.mp hm with he | hm
      · omega
      · exact ha.2 (mem_union_left _ hm)
    · intro hm
      rcases mem_insert.mp hm with he | hm
      · apply ha.1
        exact mem_union_right _ (mem_image.mpr ⟨k,hk,he⟩)
      · exact hI.2 k hk hm

theorem addable_of_insert {n : ℕ} {I : Finset ℕ} {i : ℕ}
    (hI : Admissible n (insert i I)) (hi : i ∉ I) : Addable I i := by
  constructor
  · intro hm
    rcases mem_union.mp hm with hm | hm
    · exact hi hm
    · obtain ⟨k,hk,he⟩ := mem_image.mp hm
      exact hI.2 k (mem_insert_of_mem hk) (he ▸ mem_insert_self i I)
  · intro hm
    rcases mem_union.mp hm with hm | hm
    · exact hI.2 i (mem_insert_self i I) (mem_insert_of_mem hm)
    · obtain ⟨k,hk,he⟩ := mem_image.mp hm
      have hk' : k=i := by omega
      exact hi (hk' ▸ hk)

theorem deleted_card {n : ℕ} {I : Finset ℕ} (hI : Admissible n I) :
    (deleted I).card=2*I.card := by
  have hd : Disjoint I (I.image Nat.succ) := by
    apply disjoint_left.mpr
    intro k hk hm
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hm
    exact hI.2 j hj hk
  rw [deleted,card_union_of_disjoint hd,card_image_of_injective _ Nat.succ_injective]
  omega

theorem deleted_subset {n : ℕ} {I : Finset ℕ} (hI : Admissible n I) : deleted I ⊆ range (n+2) := by
  intro k hk
  rcases mem_union.mp hk with hk | hk
  · have hh := mem_Icc.mp (hI.1 hk)
    exact mem_range.mpr (by omega)
  · obtain ⟨j,hj,rfl⟩ := mem_image.mp hk
    have hh := mem_Icc.mp (hI.1 hj)
    exact mem_range.mpr (by omega)

/-- The precise number of free coordinate classes before evaluating constant endpoints. -/
theorem available_card {n : ℕ} {I : Finset ℕ} (hI : Admissible n I) :
    (available I (n+2)).card+2*I.card=n+2 := by
  have hh := card_sdiff_add_card_eq_card (deleted_subset hI)
  rw [deleted_card hI,card_range] at hh
  exact hh

#print axioms Admissible
#print axioms deleted
#print axioms available
#print axioms coordinate
#print axioms Addable
#print axioms faceIndex
#print axioms deleted_insert
#print axioms available_insert
#print axioms available_mono
#print axioms available_insert_card
#print axioms coordinate_insert_after
#print axioms coordinate_insert_before
#print axioms coordinate_separated
#print axioms zero_available
#print axioms coordinate_positive
#print axioms faceIndex_insert_after
#print axioms faceIndex_insert_before
#print axioms faceIndex_separated
#print axioms faceIndex_valid
#print axioms admissible_pair
#print axioms admissible_insert
#print axioms addable_of_insert
#print axioms deleted_card
#print axioms deleted_subset
#print axioms available_card

end Verification.PathCompression
