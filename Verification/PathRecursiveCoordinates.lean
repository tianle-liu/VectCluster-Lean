/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathSignCompression
import Verification.PathConfigRecursion

/-!
# Path Recursive Coordinates

Literal coordinate and incidence comparisons under first-vertex deletion.
These are comparisons of the actual path zero sets, not assumed block conjugacies.
-/

namespace Verification.PathRecursiveCoordinates

open Classical Verification.PathCompression Verification.PathRhoConfiguration Verification.PathCochains
  Verification.PathSignCompression Verification.PathConfigRecursion

theorem rank_insert (I : Finset ℕ) (i j : ℕ) (hi : i ∉ I) :
    rank (insert i I) j=if i<j then rank I j+1 else rank I j := by
  by_cases hij : i<j
  · have hn : i ∉ I.filter (· < j) := by simp [hi]
    simp only [rank,Finset.filter_insert,hij,↓reduceIte,Finset.card_insert_of_not_mem hn]
  · simp only [rank,Finset.filter_insert,hij,↓reduceIte]

/-- Every earlier zero removes exactly two original coordinate positions. -/
theorem coordinate_rank {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)
    (j : ℕ) (hj : Addable I j) : coordinate I j+2*rank I j=j := by
  induction I using Finset.induction_on with
  | empty => simp [coordinate,available,deleted,rank]
  | @insert i I hi ih =>
    have hsub : I ⊆ insert i I := Finset.subset_insert _ _
    have hA : Admissible n I := admissible_mono hI hsub
    have hj' : Addable I j := addable_mono hsub hj
    have hc := ih hA hj'
    rw [rank_insert I i j hi]
    by_cases hji : j ≤ i
    · rw [if_neg (by omega),coordinate_insert_before I i j hji]
      exact hc
    · have hni : j ≠ i+1 := by
        intro he
        apply hj.1
        rw [deleted_insert,he]
        exact Finset.mem_insert_self _ _
      have hij : i+2 ≤ j := by omega
      have hai : Addable I i := addable_of_insert hI hi
      have hh := coordinate_insert_after I i j hai hij
      rw [if_pos (by omega)]
      omega

theorem rank_shift (k : ℕ) (I : Finset ℕ) (j : ℕ) :
    rank (shift k I) (j+k)=rank I j := by
  have he : (shift k I).filter (· < j+k)=shift k (I.filter (· < j)) := by
    ext x
    simp only [shift,Finset.mem_filter,Finset.mem_image]
    constructor
    · rintro ⟨⟨i,hi,rfl⟩,hij⟩
      exact ⟨i,⟨hi,by omega⟩,rfl⟩
    · rintro ⟨i,⟨hi,hij⟩,rfl⟩
      exact ⟨⟨i,hi,rfl⟩,by omega⟩
  rw [rank,he,shift_card]
  rfl

theorem deleted_shift (k : ℕ) (I : Finset ℕ) :
    deleted (shift k I)=shift k (deleted I) := by
  simp only [deleted,shift,Finset.image_union,Finset.image_image]
  congr 1
  apply Finset.image_congr
  intro i _
  simp only [Function.comp_def]
  omega

theorem addable_shift (k : ℕ) {I : Finset ℕ} {j : ℕ} (hj : Addable I j) :
    Addable (shift k I) (j+k) := by
  constructor
  · rw [deleted_shift]
    simpa only [shift,Finset.mem_image,Nat.add_left_inj,exists_eq_right] using hj.1
  · rw [deleted_shift]
    have he : j+k+1=(j+1)+k := by omega
    rw [he]
    simpa only [shift,Finset.mem_image,Nat.add_left_inj,exists_eq_right] using hj.2

/-- Before imposing a first zero, removing the first coordinate shifts every face once. -/
theorem open_coordinate {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)
    (j : ℕ) (hj : Addable I j) : coordinate (shift 1 I) (j+1)=coordinate I j+1 := by
  have h₁ := coordinate_rank hI j hj
  have h₂ := coordinate_rank (shift_admissible hI 1) (j+1) (addable_shift 1 hj)
  rw [rank_shift] at h₂
  omega

theorem open_faceIndex {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)
    (j : ℕ) (hpos : 0<j) (hj : Addable I j) :
    faceIndex (shift 1 I) (j+1)=faceIndex I j+1 := by
  have hh := open_coordinate hI j hj
  have hp := coordinate_positive hI hpos
  unfold faceIndex
  omega

theorem closed_addable {I : Finset ℕ} {j : ℕ} (hpos : 0<j) (hj : Addable I j) :
    Addable (insert 1 (shift 2 I)) (j+2) := by
  have hh := addable_shift 2 hj
  constructor
  · rw [deleted_insert]
    intro hm
    rcases Finset.mem_insert.mp hm with he | hm
    · omega
    rcases Finset.mem_insert.mp hm with he | hm
    · omega
    exact hh.1 hm
  · rw [deleted_insert]
    intro hm
    rcases Finset.mem_insert.mp hm with he | hm
    · omega
    rcases Finset.mem_insert.mp hm with he | hm
    · omega
    exact hh.2 hm

theorem closed_rank (I : Finset ℕ) (j : ℕ) :
    rank (insert 1 (shift 2 I)) (j+2)=rank I j+1 := by
  have hn : 1 ∉ shift 2 I := by
    intro hm
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hm
    omega
  rw [rank_insert _ _ _ hn,if_pos (by omega),rank_shift]

/-- Imposing the first zero cancels precisely the two-position shift. -/
theorem closed_coordinate {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)
    (j : ℕ) (hpos : 0<j) (hj : Addable I j) :
    coordinate (insert 1 (shift 2 I)) (j+2)=coordinate I j := by
  have h₁ := coordinate_rank hI j hj
  have h₂ := coordinate_rank (closed_insert_admissible n ⟨I,hI⟩) (j+2)
    (closed_addable hpos hj)
  change coordinate (insert 1 (shift 2 I)) (j+2)+2*rank (insert 1 (shift 2 I)) (j+2)=j+2 at h₂
  rw [closed_rank] at h₂
  omega

theorem closed_faceIndex {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)
    (j : ℕ) (hpos : 0<j) (hj : Addable I j) :
    faceIndex (insert 1 (shift 2 I)) (j+2)=faceIndex I j := by
  unfold faceIndex
  rw [closed_coordinate hI j hpos hj]

#print axioms rank_insert
#print axioms coordinate_rank
#print axioms rank_shift
#print axioms deleted_shift
#print axioms addable_shift
#print axioms open_coordinate
#print axioms open_faceIndex
#print axioms closed_addable
#print axioms closed_rank
#print axioms closed_coordinate
#print axioms closed_faceIndex

end Verification.PathRecursiveCoordinates
