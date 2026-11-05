/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.BinaryPfisterBasis

/-!
# Binary Pfister Words

The unimodular binary basis consists of the literal products
∏(z_i-1) in the integral group ring.
-/
noncomputable section
open scoped Classical BigOperators
namespace Verification.BinaryPfisterWords
open Verification.BinaryPfisterBasis
variable (α : Type*) [Fintype α]

def character (A : Finset α) : BinaryPfisterBasis.Ring α := MonoidAlgebra.of ℤ _ (indexEquiv α A)

theorem character_empty : character α ∅ = 1 := by
  have he : indexEquiv α ∅ = 1 := by
    apply Multiplicative.toAdd.injective
    funext a
    simp [indexEquiv,BooleanCubeCoordinates.cubeEquiv,BooleanAffineLattice.vector]
  rw [character,he,map_one]

theorem character_insert (i : α) (A : Finset α) (hi : i ∉ A) :
    character α (insert i A) = character α {i} * character α A := by
  have he : indexEquiv α (insert i A) = indexEquiv α {i} * indexEquiv α A := by
    apply Multiplicative.toAdd.injective
    funext a
    change BooleanAffineLattice.vector (insert i A) a =
      BooleanAffineLattice.vector {i} a + BooleanAffineLattice.vector A a
    by_cases ha : a = i
    · subst a
      simp [BooleanAffineLattice.vector,hi]
    · simp [BooleanAffineLattice.vector,ha]
  exact congrArg (MonoidAlgebra.of ℤ (BinaryPfisterBasis.Group α)) he |>.trans (map_mul _ _ _)

theorem character_product (A : Finset α) :
    ∏ i ∈ A, character α {i} = character α A := by
  induction A using Finset.induction_on with
  | empty => simp [character_empty]
  | @insert i A hi ih => rw [Finset.prod_insert hi,ih,character_insert α i A hi]

def word (A : Finset α) : BinaryPfisterBasis.Ring α := ∏ i ∈ A, (character α {i} - 1)

theorem word_expansion (A : Finset α) :
    word α A = ∑ B ∈ A.powerset, ((-1:ℤ)^(A.card-B.card)) • character α B := by
  simp only [word,sub_eq_add_neg,Finset.prod_add,character_product,Finset.prod_const]
  apply Finset.sum_congr rfl
  intro B hB
  have hs : B ⊆ A := Finset.mem_powerset.mp hB
  rw [Finset.card_sdiff hs]
  simp [zsmul_eq_mul,mul_comm]

theorem characterEquiv_sum (f : Finset α → ℤ) :
    characterEquiv α f = ∑ A : Finset α, f A • character α A := by
  have he : f = ∑ A : Finset α, f A • Pi.single A 1 := by
    funext B
    simp [Pi.single_apply]
  conv_lhs => rw [he,map_sum]
  apply Finset.sum_congr rfl
  intro A _
  rw [map_smul,character_single]
  rfl

theorem basis_word (A : Finset α) : basis α A = word α A := by
  simp only [BinaryPfisterBasis.basis,Basis.map_apply,Pi.basisFun_apply]
  change characterEquiv α (transform α (Pi.single A 1)) = _
  rw [characterEquiv_sum,word_expansion]
  simp only [transform_single,matrix,ite_smul,zero_smul]
  rw [← Finset.sum_filter]
  have he : Finset.univ.filter (fun B : Finset α => B ⊆ A) = A.powerset := by
    ext B
    simp
  rw [he]

#print axioms character
#print axioms character_empty
#print axioms character_insert
#print axioms character_product
#print axioms word
#print axioms word_expansion
#print axioms characterEquiv_sum
#print axioms basis_word
end Verification.BinaryPfisterWords
