/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.EvenWittPfisterResidue

/-!
# Even Witt Color Vanishing

The actual new color relation kills precisely the forbidden frozen
Pfister factor in the target of a coordinate face.
-/
noncomputable section
open scoped Classical BigOperators
namespace Verification.EvenWittColorVanishing
open MonoidAlgebra Verification.OriginalWittQuotient Verification.EvenWittPfisterResidue
variable {V C : Type*} (c : V → C)

theorem frozen_value (J : Finset V) (j : V) (hj : j ∈ J) :
    Ideal.Quotient.mk (relationIdeal (EvenWittColumns.frozenMatrix c) J) (of ℤ _ (frozen (c j))) = -1 := by
  have hg : columnVector (EvenWittColumns.frozenMatrix c) j = frozen (V := V) (c j) := by
    apply Multiplicative.toAdd.injective
    funext a
    cases a with
    | inl v => simp [columnVector,EvenWittColumns.frozenMatrix,frozen,Pi.single_apply]
    | inr a => simp [columnVector,EvenWittColumns.frozenMatrix,frozen,Pi.single_apply,apply_ite,eq_comm]
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr (column_relation (EvenWittColumns.frozenMatrix c) J ⟨j,hj⟩)
  rw [map_add,map_one,hg] at h
  exact eq_neg_of_add_eq_zero_left h

theorem word_zero (J A : Finset V) (F : Finset C) (j : V) (hj : j ∈ J) (hc : c j ∈ F) :
    quotientWord c J A F = 0 := by
  change Ideal.Quotient.mk _ (mutableWord A * ∏ a ∈ F, ((-1:ℤ) • of ℤ _ (frozen a) - 1)) = 0
  rw [map_mul,map_prod]
  have hz : (∏ a ∈ F, Ideal.Quotient.mk (relationIdeal (EvenWittColumns.frozenMatrix c) J)
      ((-1:ℤ) • of ℤ _ (frozen a) - 1)) = 0 := by
    apply Finset.prod_eq_zero hc
    rw [map_sub,map_one,map_zsmul,frozen_value c J j hj]
    simp
  rw [hz,mul_zero]

theorem residue (I J : Finset V) (j : V) (hIJ : I ⊆ J) (hi : j ∉ I) (hj : j ∈ J)
    (A : Finset V) (F : Finset C) :
    OriginalWittQuotient.residue (EvenWittColumns.frozenMatrix c) I J j hIJ hi (fun _ => rfl)
      (quotientWord c I A F) =
      if j ∈ A ∧ c j ∉ F then quotientWord c J (A.erase j) F else 0 := by
  rw [EvenWittPfisterResidue.residue c I J j hIJ hi hj A F]
  by_cases hA : j ∈ A
  · rw [if_pos hA]
    by_cases hF : c j ∈ F
    · rw [if_neg (by simp [hF]),word_zero c J (A.erase j) F j hj hF]
    · rw [if_pos ⟨hA,hF⟩]
  · rw [if_neg hA,if_neg (by simp [hA])]

#print axioms frozen_value
#print axioms word_zero
#print axioms residue
end Verification.EvenWittColorVanishing
