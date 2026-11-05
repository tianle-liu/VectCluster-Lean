/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathFirstVertexSupport

/-!
# Path Config Recursion

Actual first-vertex recursion of the original independent path zero sets.
-/

namespace Verification.PathConfigRecursion

open Classical Verification.PathCompression Verification.PathCochains

noncomputable def shift (k : ℕ) (I : Finset ℕ) : Finset ℕ := I.image (fun i => i+k)
noncomputable def down (k : ℕ) (I : Finset ℕ) : Finset ℕ := I.image (fun i => i-k)

theorem down_shift (k : ℕ) (I : Finset ℕ) : down k (shift k I)=I := by
  simp only [down,shift,Finset.image_image,Function.comp_def,Nat.add_sub_cancel,Finset.image_id]
  exact Finset.image_id

theorem shift_down (k : ℕ) (I : Finset ℕ) (hI : ∀ i ∈ I, k ≤ i) : shift k (down k I)=I := by
  rw [shift,down,Finset.image_image]
  calc
    I.image ((fun i => i+k) ∘ (fun i => i-k))=I.image id := by
      apply Finset.image_congr
      intro i hi
      exact Nat.sub_add_cancel (hI i hi)
    _=I := Finset.image_id

theorem shift_admissible {n : ℕ} {I : Finset ℕ} (hI : Admissible n I) (k : ℕ) :
    Admissible (n+k) (shift k I) := by
  constructor
  · intro j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    have hh := Finset.mem_Icc.mp (hI.1 hi)
    exact Finset.mem_Icc.mpr (by omega)
  · intro j hj hj'
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨l,hl,he⟩ := Finset.mem_image.mp hj'
    have he' : l=i+1 := by omega
    exact hI.2 i hi (he' ▸ hl)

theorem down_admissible {n k : ℕ} {I : Finset ℕ} (hI : Admissible (n+k) I)
    (hlo : ∀ i ∈ I, k < i) : Admissible n (down k I) := by
  constructor
  · intro j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    have hh := Finset.mem_Icc.mp (hI.1 hi)
    have hlow := hlo i hi
    exact Finset.mem_Icc.mpr (by omega)
  · intro j hj hj'
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨l,hl,he⟩ := Finset.mem_image.mp hj'
    have hi' := hlo i hi
    have hl' := hlo l hl
    have he' : l=i+1 := by omega
    exact hI.2 i hi (he' ▸ hl)

theorem shift_card (k : ℕ) (I : Finset ℕ) : (shift k I).card=I.card := by
  exact Finset.card_image_of_injective _ (fun _ _ h => Nat.add_right_cancel h)

abbrev OpenConfig (n : ℕ) := {I : Config (n+1) // 1 ∉ I.val}
abbrev ClosedConfig (n : ℕ) := {I : Config (n+2) // 1 ∈ I.val}

noncomputable def openUp (n : ℕ) (I : Config n) : OpenConfig n :=
  ⟨⟨shift 1 I.val,shift_admissible I.property 1⟩,by
    intro h
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp h
    have hh := Finset.mem_Icc.mp (I.property.1 hi)
    omega⟩

theorem open_lower (n : ℕ) (I : OpenConfig n) (i : ℕ) (hi : i ∈ I.val.val) : 1 < i := by
  have hh := Finset.mem_Icc.mp (I.val.property.1 hi)
  have hn : i ≠ 1 := fun h => I.property (h ▸ hi)
  omega

noncomputable def openDown (n : ℕ) (I : OpenConfig n) : Config n :=
  ⟨down 1 I.val.val,down_admissible I.val.property (open_lower n I)⟩

noncomputable def openEquiv (n : ℕ) : OpenConfig n ≃ Config n where
  toFun := openDown n
  invFun := openUp n
  left_inv I := by
    apply Subtype.ext
    apply Subtype.ext
    exact shift_down 1 I.val.val (fun i hi => Nat.le_of_lt (open_lower n I i hi))
  right_inv I := by
    apply Subtype.ext
    exact down_shift 1 I.val

theorem closed_lower (n : ℕ) (I : ClosedConfig n) (i : ℕ) (hi : i ∈ I.val.val.erase 1) : 2 < i := by
  have hh := Finset.mem_Icc.mp (I.val.property.1 (Finset.mem_of_mem_erase hi))
  have hn := (Finset.mem_erase.mp hi).1
  have h₂ : 2 ∉ I.val.val := I.val.property.2 1 I.property
  have hn₂ : i ≠ 2 := fun h => h₂
    ((congrArg (fun t : ℕ => t ∈ I.val.val) h).mp (Finset.mem_of_mem_erase hi))
  omega

theorem closed_insert_admissible (n : ℕ) (I : Config n) :
    Admissible (n+2) (insert 1 (shift 2 I.val)) := by
  have hs := shift_admissible I.property 2
  constructor
  · apply Finset.insert_subset_iff.mpr
    exact ⟨Finset.mem_Icc.mpr (by omega),hs.1⟩
  · intro j hj hj'
    rcases Finset.mem_insert.mp hj with rfl | hj
    · have hmem : 2 ∈ shift 2 I.val := Finset.mem_of_mem_insert_of_ne hj' (by omega)
      obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hmem
      have hh := Finset.mem_Icc.mp (I.property.1 hi)
      omega
    · have hnext : j+1 ∈ shift 2 I.val := by
        apply Finset.mem_of_mem_insert_of_ne hj'
        have hh := Finset.mem_Icc.mp (hs.1 hj)
        omega
      exact hs.2 j hj hnext

noncomputable def closedUp (n : ℕ) (I : Config n) : ClosedConfig n :=
  ⟨⟨insert 1 (shift 2 I.val),closed_insert_admissible n I⟩,Finset.mem_insert_self _ _⟩

noncomputable def closedDown (n : ℕ) (I : ClosedConfig n) : Config n :=
  ⟨down 2 (I.val.val.erase 1),down_admissible (eraseConfig I.val 1).property (closed_lower n I)⟩

theorem one_not_shift_two (n : ℕ) (I : Config n) : 1 ∉ shift 2 I.val := by
  intro h
  obtain ⟨i,_,he⟩ := Finset.mem_image.mp h
  omega

noncomputable def closedEquiv (n : ℕ) : ClosedConfig n ≃ Config n where
  toFun := closedDown n
  invFun := closedUp n
  left_inv I := by
    apply Subtype.ext
    apply Subtype.ext
    change insert 1 (shift 2 (down 2 (I.val.val.erase 1)))=I.val.val
    rw [shift_down 2 _ (fun i hi => Nat.le_of_lt (closed_lower n I i hi)),Finset.insert_erase I.property]
  right_inv I := by
    apply Subtype.ext
    change down 2 ((insert 1 (shift 2 I.val)).erase 1)=I.val
    rw [Finset.erase_insert (one_not_shift_two n I),down_shift]

theorem open_card (n : ℕ) (I : OpenConfig n) : (openEquiv n I).val.card=I.val.val.card := by
  have he := congrArg (fun J : OpenConfig n => J.val.val.card) ((openEquiv n).symm_apply_apply I)
  change (shift 1 (openEquiv n I).val).card=I.val.val.card at he
  simpa only [shift_card] using he

theorem closed_card (n : ℕ) (I : ClosedConfig n) : (closedEquiv n I).val.card+1=I.val.val.card := by
  have he := congrArg (fun J : ClosedConfig n => J.val.val.card) ((closedEquiv n).symm_apply_apply I)
  change (insert 1 (shift 2 (closedEquiv n I).val)).card=I.val.val.card at he
  simpa only [Finset.card_insert_of_not_mem (one_not_shift_two n (closedEquiv n I)),shift_card] using he

#print axioms shift
#print axioms down
#print axioms down_shift
#print axioms shift_down
#print axioms shift_admissible
#print axioms down_admissible
#print axioms shift_card
#print axioms OpenConfig
#print axioms ClosedConfig
#print axioms openUp
#print axioms open_lower
#print axioms openDown
#print axioms openEquiv
#print axioms closed_lower
#print axioms closed_insert_admissible
#print axioms closedUp
#print axioms closedDown
#print axioms one_not_shift_two
#print axioms closedEquiv
#print axioms open_card
#print axioms closed_card

end Verification.PathConfigRecursion
