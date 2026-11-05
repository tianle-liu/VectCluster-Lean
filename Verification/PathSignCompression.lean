/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathAffineIntertwiner
import Verification.PathCochains

/-!
# Path Sign Compression

Deleting original adjacent coordinate pairs preserves parity. This
identifies every compressed normal's affine-sign factor with its original vertex.
-/

namespace Verification.PathSignCompression

open Classical Verification.PathCompression Verification.PathCochains
  Verification.PathAffineIntertwiner

variable {R : Type*} [CommRing R]

theorem deleted_mono {I J : Finset ℕ} (h : I ⊆ J) : deleted I ⊆ deleted J := by
  exact Finset.union_subset_union h (Finset.image_subset_image h)

theorem addable_mono {I J : Finset ℕ} (h : I ⊆ J) {j : ℕ} (hj : Addable J j) : Addable I j :=
  ⟨fun hm => hj.1 (deleted_mono h hm),fun hm => hj.2 (deleted_mono h hm)⟩

/-- The actual surviving-coordinate position has the same parity as its original position. -/
theorem coordinate_parity {n : ℕ} {I : Finset ℕ} (hI : Admissible n I)
    (j : ℕ) (hj : Addable I j) : coordinate I j % 2=j % 2 := by
  induction I using Finset.induction_on with
  | empty => simp [coordinate,available,deleted]
  | @insert i I hi ih =>
    have hsub : I ⊆ insert i I := Finset.subset_insert _ _
    have hA : Admissible n I := admissible_mono hI hsub
    have hj' : Addable I j := addable_mono hsub hj
    have hpar := ih hA hj'
    by_cases hji : j ≤ i
    · rw [coordinate_insert_before I i j hji]
      exact hpar
    · have hni : j ≠ i+1 := by
        intro he
        apply hj.1
        rw [deleted_insert]
        rw [he]
        exact Finset.mem_insert_self _ _
      have hij : i+2 ≤ j := by omega
      have hai : Addable I i := addable_of_insert hI hi
      have hh := coordinate_insert_after I i j hai hij
      omega

/-- The sign chosen for an original coordinate by the two parity parameters. -/
def vertexFactor (g : R) (a b : Bool) (j : ℕ) : R :=
  if j%2=0 then (if a then g else 1) else (if b then g else 1)

theorem normalFactor_parity (g : R) (a b : Bool) (i : ℕ) :
    normalFactor g a b i=if i%2=0 then (if b then g else 1) else (if a then g else 1) := by
  induction i generalizing a b with
  | zero => rfl
  | succ i ih =>
    rw [normalFactor,ih b a]
    by_cases hi : i%2=0
    · have hnext : (i+1)%2 ≠ 0 := by omega
      simp only [hi,hnext,↓reduceIte]
    · have hnext : (i+1)%2=0 := by omega
      simp only [hi,hnext,↓reduceIte]

/-- The compressed-face scalar is exactly the scalar of the actual original normal vertex. -/
theorem normalFactor_compression (g : R) (a b : Bool) {n : ℕ} {I : Finset ℕ}
    (hI : Admissible n I) (j : ℕ) (hpos : 0 < j) (hj : Addable I j) :
    normalFactor g a b (faceIndex I j)=vertexFactor g a b j := by
  have hp := coordinate_positive hI hpos
  have he := coordinate_parity hI j hj
  rw [normalFactor_parity,vertexFactor]
  by_cases hjp : j%2=0
  · have hf : faceIndex I j%2 ≠ 0 := by unfold faceIndex; omega
    simp only [hjp,hf,↓reduceIte]
  · have hf : faceIndex I j%2=0 := by unfold faceIndex; omega
    simp only [hjp,hf,↓reduceIte]

#print axioms deleted_mono
#print axioms addable_mono
#print axioms coordinate_parity
#print axioms vertexFactor
#print axioms normalFactor_parity
#print axioms normalFactor_compression

end Verification.PathSignCompression
