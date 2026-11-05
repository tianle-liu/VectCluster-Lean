/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathClosedEmbedding

/-!
# Path Closed Differential

Assembly of the literal recursive closed diagonal from all original faces.
-/

namespace Verification.PathClosedDifferential

open Classical Verification.PathCompression Verification.PathCochains
  Verification.PathRhoConfiguration Verification.PathConfigRecursion
  Verification.PathRecursiveFaces Verification.PathClosedEmbedding

variable {R : Type*} [CommRing R]

theorem shift_erase (k : ℕ) (I : Finset ℕ) (j : ℕ) :
    (shift k I).erase (j+k)=shift k (I.erase j) := by
  ext x
  simp only [shift,Finset.mem_erase,Finset.mem_image]
  constructor
  · rintro ⟨hne,⟨i,hi,rfl⟩⟩
    exact ⟨i,⟨by omega,hi⟩,rfl⟩
  · rintro ⟨i,⟨hne,hi⟩,rfl⟩
    exact ⟨by omega,⟨i,hi,rfl⟩⟩

theorem closedUp_erase (n : ℕ) (I : Config n) (j : ℕ) :
    eraseConfig (closedUp n I).val (j+2)=(closedUp n (eraseConfig I j)).val := by
  apply Subtype.ext
  change (insert 1 (shift 2 I.val)).erase (j+2)=insert 1 (shift 2 (I.val.erase j))
  rw [Finset.erase_insert_of_ne (by omega),shift_erase]

theorem differential_open (g ρ : R) (n : ℕ) (x : Total (R := R) n)
    (J : Config (n+2)) (hJ : 1 ∉ J.val) :
    (differential g ρ (n+2) (extension n x)) J=0 := by
  apply Subtype.ext
  change ambientDifferential g ρ (n+2) (inclusion (n+2) (extension n x)) J=0
  rw [ambientDifferential_apply]
  apply Finset.sum_eq_zero
  intro j _
  have hn : 1 ∉ (eraseConfig J j).val := fun hm => hJ (Finset.mem_of_mem_erase hm)
  change faceMap g ρ (eraseConfig J j).val j ((extension n x) (eraseConfig J j)).val=0
  rw [extension_open n x _ hn]
  exact map_zero _

/-- The full assembled closed diagonal equals g times the shorter actual differential. -/
theorem differential_closed (g ρ : R) (n : ℕ) (x : Total (R := R) n) (J : Config n) :
    ((differential g ρ (n+2) (extension n x)) (closedUp n J).val).val=
      g • ((differential g ρ n x) J).val := by
  change ambientDifferential g ρ (n+2) (inclusion (n+2) (extension n x)) (closedUp n J).val=
    g • ambientDifferential g ρ n (inclusion n x) J
  rw [ambientDifferential_apply,ambientDifferential_apply]
  change (∑ j ∈ insert 1 (shift 2 J.val),
    faceMap g ρ (eraseConfig (closedUp n J).val j).val j
      ((extension n x) (eraseConfig (closedUp n J).val j)).val)=_
  rw [Finset.sum_insert (one_not_shift_two n J)]
  have hz : ((extension n x) (eraseConfig (closedUp n J).val 1)).val=0 := by
    rw [extension_open n x _ (Finset.not_mem_erase _ _)]
    rfl
  rw [hz,map_zero,zero_add]
  unfold shift
  rw [Finset.sum_image (by intro i _ j _ he; exact Nat.add_right_cancel he),Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [closedUp_erase,extension_closed]
  have he : closedDown n (closedUp n (eraseConfig J j))=eraseConfig J j :=
    (closedEquiv n).apply_symm_apply _
  rw [he]
  have hi : insert j (eraseConfig J j).val=J.val := Finset.insert_erase hj
  have ha := addable_of_insert (hi.symm ▸ J.property) (Finset.not_mem_erase _ _)
  have hf := closed_face g ρ (eraseConfig J j).property j (Finset.mem_Icc.mp (J.property.1 hj)).1 ha
  change faceMap g ρ (insert 1 (shift 2 (eraseConfig J j).val)) (j+2) (x (eraseConfig J j)).val=_
  rw [hf]
  rfl

theorem differential_extension (g ρ : R) (n : ℕ) :
    (differential g ρ (n+2)).comp (extension n)=
      (extension n).comp (g • differential g ρ n) := by
  apply LinearMap.ext
  intro x
  funext J
  by_cases hJ : 1 ∈ J.val
  · have he : (closedUp n (closedDown n ⟨J,hJ⟩)).val=J :=
      congrArg Subtype.val ((closedEquiv n).symm_apply_apply ⟨J,hJ⟩)
    apply Subtype.ext
    change ((differential g ρ (n+2) (extension n x)) J).val=
      ((extension n (g • differential g ρ n x)) J).val
    rw [← he,differential_closed,extension_closed]
    have hd : closedDown n (closedUp n (closedDown n ⟨J,hJ⟩))=closedDown n ⟨J,hJ⟩ :=
      (closedEquiv n).apply_symm_apply _
    rw [hd]
    rfl
  · change (differential g ρ (n+2) (extension n x)) J=
      (extension n (g • differential g ρ n x)) J
    rw [differential_open g ρ n x J hJ,extension_open n _ J hJ]

theorem differential_closedSupport (g ρ : R) (n : ℕ) :
    closedSupport (R := R) n ≤ (closedSupport n).comap (differential g ρ (n+2)) := by
  rintro _ ⟨x,rfl⟩
  exact ⟨g • differential g ρ n x, (LinearMap.congr_fun (differential_extension g ρ n) x).symm⟩

#print axioms shift_erase
#print axioms closedUp_erase
#print axioms differential_open
#print axioms differential_closed
#print axioms differential_extension
#print axioms differential_closedSupport

end Verification.PathClosedDifferential
