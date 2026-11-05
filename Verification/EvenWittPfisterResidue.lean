/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SignedProjectionProducts
import Verification.EvenWittCoordinateSplit

/-!
# Even Witt Pfister Residue

The actual coordinate residue contracts the mutable Pfister factor
with coefficient one. The target relation kills the newly selected color
factor. These are identities in the literal quotient rings.
-/
noncomputable section
open scoped Classical BigOperators
namespace Verification.EvenWittPfisterResidue
open MonoidAlgebra Verification.OriginalWittQuotient Verification.SignedGroupRingFace
variable {V C : Type*}

def frozen (a : C) : Group V C := Multiplicative.ofAdd (Pi.single (Sum.inr a) 1)

def mutableWord (A : Finset V) : Ambient V C := ∏ i ∈ A, (of ℤ _ (normalVector i) - 1)

def frozenWord (F : Finset C) : Ambient V C := ∏ a ∈ F, ((-1:ℤ) • of ℤ _ (frozen a) - 1)

def word (A : Finset V) (F : Finset C) : Ambient V C := mutableWord A * frozenWord F

theorem mutable_kernel (j i : V) (h : i ≠ j) : coordinate (C := C) j (normalVector i) = 1 := by
  simp [coordinate,normalVector,Pi.single_apply,h,Ne.symm h]

theorem frozen_kernel (j : V) (a : C) : coordinate j (frozen a) = 1 := by
  simp [coordinate,frozen,Pi.single_apply]

theorem normal_nontrivial (j : V) : coordinate (C := C) j (normalVector j) ≠ 1 := by
  change (Pi.single (Sum.inl j) (1:ZMod 2) : Bits V C) (Sum.inl j) ≠ 0
  simp only [Pi.single_eq_same]
  decide

theorem mutable_projection_zero (j : V) (A : Finset V) (hj : j ∉ A) :
    projection (coordinate (C := C) j) (mutableWord A) = 0 := by
  have h := SignedProjectionProducts.signed_product_zero (coordinate (C := C) j) A
    (fun i => normalVector i) (fun _ => (1:ℤ)) (fun i hi => mutable_kernel j i (by intro e; exact hj (e ▸ hi)))
  simpa [mutableWord] using h

theorem mutable_projection (j : V) (A : Finset V) (hj : j ∈ A) :
    projection (coordinate (C := C) j) (mutableWord A) =
      of ℤ _ (normalVector j) * mutableWord (A.erase j) := by
  have he : mutableWord (C := C) A = (of ℤ _ (normalVector j) - 1) * mutableWord (A.erase j) := by
    unfold mutableWord
    conv_lhs => rw [← Finset.insert_erase hj,Finset.prod_insert (Finset.not_mem_erase j A)]
  rw [he]
  have hp := SignedProjectionProducts.signed_product (coordinate (C := C) j) (A.erase j)
    (fun i => normalVector i) (fun _ => (1:ℤ))
    (fun i hi => mutable_kernel j i (Finset.ne_of_mem_erase hi))
    (of ℤ _ (normalVector j) - 1)
  rw [map_sub,SignedProjectionProducts.one_zero,
    SignedProjectionProducts.character _ _ (normal_nontrivial (C := C) j)] at hp
  simpa only [mutableWord,one_smul,sub_zero] using hp

theorem word_projection (j : V) (A : Finset V) (F : Finset C) :
    projection (coordinate j) (word A F) =
      if j ∈ A then of ℤ _ (normalVector j) * word (A.erase j) F else 0 := by
  have hp := SignedProjectionProducts.signed_product (coordinate (C := C) j) F frozen
    (fun _ => (-1:ℤ)) (fun a _ => frozen_kernel j a) (mutableWord (C := C) A)
  change projection (coordinate j) (word A F) = _ at hp
  rw [hp]
  by_cases hj : j ∈ A
  · rw [if_pos hj,mutable_projection j A hj,mul_assoc]
    rfl
  · rw [if_neg hj,mutable_projection_zero j A hj,zero_mul]

variable (c : V → C)

def quotientWord (I A : Finset V) (F : Finset C) : Stratum (EvenWittColumns.frozenMatrix c) I :=
  Ideal.Quotient.mk _ (word A F)

theorem normal_value (J : Finset V) (j : V) (hj : j ∈ J) :
    Ideal.Quotient.mk (relationIdeal (EvenWittColumns.frozenMatrix c) J) (of ℤ _ (normalVector j)) = 1 := by
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr (normal_relation (EvenWittColumns.frozenMatrix c) J ⟨j,hj⟩)
  simpa only [map_sub,map_one,sub_eq_zero] using h

theorem residue (I J : Finset V) (j : V) (hIJ : I ⊆ J) (hi : j ∉ I) (hj : j ∈ J)
    (A : Finset V) (F : Finset C) :
    OriginalWittQuotient.residue (EvenWittColumns.frozenMatrix c) I J j hIJ hi (fun _ => rfl)
      (quotientWord c I A F) =
      if j ∈ A then quotientWord c J (A.erase j) F else 0 := by
  rw [quotientWord,residue_mk,word_projection]
  by_cases hA : j ∈ A
  · rw [if_pos hA,if_pos hA,map_mul,normal_value c J j hj,one_mul]
    rfl
  · rw [if_neg hA,if_neg hA,map_zero]

#print axioms frozen
#print axioms mutableWord
#print axioms frozenWord
#print axioms word
#print axioms mutable_kernel
#print axioms frozen_kernel
#print axioms normal_nontrivial
#print axioms mutable_projection_zero
#print axioms mutable_projection
#print axioms word_projection
#print axioms quotientWord
#print axioms normal_value
#print axioms residue
end Verification.EvenWittPfisterResidue
