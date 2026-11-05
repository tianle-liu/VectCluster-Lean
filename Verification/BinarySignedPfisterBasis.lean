/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.BinaryPfisterWords
import Verification.SignedGroupRingTwist

/-!
# Binary Signed Pfister Basis

Allowing an integral sign for each binary coordinate gives the actual
basis ∏(ε_i z_i-1). It is transported by a proved algebra automorphism.
-/
noncomputable section
open scoped Classical BigOperators
namespace Verification.BinarySignedPfisterBasis
variable (α : Type*) [Fintype α] (u : α → ℤˣ)

def basis : Basis (Finset α) ℤ (BinaryPfisterBasis.Ring α) :=
  (BinaryPfisterBasis.basis α).map
    (SignedGroupRingTwist.equiv (BinarySignedFiber.character u)).toLinearEquiv

theorem index_singleton (i : α) : BinaryPfisterBasis.indexEquiv α {i} =
    Multiplicative.ofAdd (Pi.single i 1) := by
  apply Multiplicative.toAdd.injective
  funext a
  simp [BinaryPfisterBasis.indexEquiv,BooleanCubeCoordinates.cubeEquiv,
    BooleanAffineLattice.vector,Pi.single_apply,eq_comm]

theorem character_singleton (i : α) :
    SignedGroupRingTwist.hom (BinarySignedFiber.character u) (BinaryPfisterWords.character α {i}) =
      (u i : ℤ) • BinaryPfisterWords.character α {i} := by
  rw [BinaryPfisterWords.character,SignedGroupRingTwist.monomial,index_singleton,
    BinarySignedFiber.character_single]
  exact (Algebra.smul_def _ _).symm

theorem basis_word (A : Finset α) : basis α u A =
    ∏ i ∈ A, ((u i : ℤ) • BinaryPfisterWords.character α {i} - 1) := by
  rw [basis,Basis.map_apply,BinaryPfisterWords.basis_word]
  change SignedGroupRingTwist.hom (BinarySignedFiber.character u) (BinaryPfisterWords.word α A) = _
  rw [BinaryPfisterWords.word,map_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [map_sub,map_one,character_singleton]

#print axioms basis
#print axioms index_singleton
#print axioms character_singleton
#print axioms basis_word
end Verification.BinarySignedPfisterBasis
