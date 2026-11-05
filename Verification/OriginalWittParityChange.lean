/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalWittIntegerComplex

/-!
# Original Witt Parity Change

The literal integral Witt quotient and each actual residue depend only
on the exchange columns modulo two. No comparison of ranks or signatures
replaces the original quotient maps.
-/
noncomputable section
namespace Verification.OriginalWittParityChange
open Verification.OriginalWittQuotient
variable {V C : Type*}
variable (B B' : (V ⊕ C) → V → ℤ)
variable (h : ∀ a i, (B a i : ZMod 2) = (B' a i : ZMod 2))

include h in
theorem column_eq (i : V) : columnVector B i = columnVector B' i := by
  apply Multiplicative.toAdd.injective
  funext a
  exact h a i

include h in
theorem ideal_eq (I : Finset V) : relationIdeal B I = relationIdeal B' I := by
  have hg : generator B I = generator B' I := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => exact column_eq B B' h i.val
  unfold relationIdeal
  rw [hg]

def equiv (I : Finset V) : Stratum B I ≃ₐ[ℤ] Stratum B' I :=
  Ideal.quotientEquivAlgOfEq ℤ (ideal_eq B B' h I)

theorem equiv_mk (I : Finset V) (a : Ambient V C) :
    equiv B B' h I (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a :=
  Ideal.quotientEquivAlgOfEq_mk _ _ _

theorem residue (I J : Finset V) (j : V) (hIJ : I ⊆ J) (hj : j ∉ I)
    (hB : ∀ i : I, B (Sum.inl j) i.val = 0)
    (hB' : ∀ i : I, B' (Sum.inl j) i.val = 0) (a : Stratum B I) :
    equiv B B' h J (OriginalWittQuotient.residue B I J j hIJ hj hB a) =
      OriginalWittQuotient.residue B' I J j hIJ hj hB' (equiv B B' h I a) := by
  obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [residue_mk,equiv_mk,equiv_mk,residue_mk]

#print axioms column_eq
#print axioms ideal_eq
#print axioms equiv
#print axioms equiv_mk
#print axioms residue
end Verification.OriginalWittParityChange
