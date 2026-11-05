/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FreezingIndex
import Verification.ActualDivisorPresentation

/-!
# Freezing Original Index

The literal partition of original coordinates for a freezing divisor:
the killed vertex, remaining mutable originals, and invertible neighbors
and frozen originals.
-/
noncomputable section
namespace Verification.FreezingOriginalIndex
open Verification.FrozenAcyclicCover Verification.ActualFreezingDivisor Verification.FreezingIndex
variable (κ : Type) (n : ℕ) (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (v : Fin n)

def mutableIndex : Fin n ≃ (PUnit.{1} ⊕ Remaining κ n B v) ⊕ Neighbor κ n B v :=
  partition v (ExchangeRing.Adjacent (laterWeights κ n B) v) (by simp [ExchangeRing.Adjacent])

def originals : (Fin n ⊕ κ) ≃ PUnit.{1} ⊕ (Remaining κ n B v ⊕ (Neighbor κ n B v ⊕ κ)) :=
  (Equiv.sumCongr (mutableIndex κ n B v) (Equiv.refl κ)).trans
    ((Equiv.sumAssoc (PUnit.{1} ⊕ Remaining κ n B v) (Neighbor κ n B v) κ).trans
      (Equiv.sumAssoc PUnit.{1} (Remaining κ n B v) (Neighbor κ n B v ⊕ κ)))

theorem originals_symm_free : (originals κ n B v).symm (Sum.inl PUnit.unit) = Sum.inl v := rfl

theorem originals_symm_remaining (i : Remaining κ n B v) :
    (originals κ n B v).symm (Sum.inr (Sum.inl i)) = Sum.inl i.val := rfl

theorem originals_symm_inverted (i : Neighbor κ n B v ⊕ κ) :
    (originals κ n B v).symm (Sum.inr (Sum.inr i)) =
      Verification.ActualDivisorPresentation.invertedOriginal κ n B v i := by
  cases i <;> rfl

theorem originals_free : originals κ n B v (Sum.inl v) = Sum.inl PUnit.unit :=
  (originals κ n B v).apply_symm_apply (Sum.inl PUnit.unit)

theorem originals_remaining (i : Remaining κ n B v) :
    originals κ n B v (Sum.inl i.val) = Sum.inr (Sum.inl i) :=
  (originals κ n B v).apply_symm_apply (Sum.inr (Sum.inl i))

theorem originals_inverted (i : Neighbor κ n B v ⊕ κ) :
    originals κ n B v (Verification.ActualDivisorPresentation.invertedOriginal κ n B v i) =
      Sum.inr (Sum.inr i) := by
  rw [← originals_symm_inverted]
  exact (originals κ n B v).apply_symm_apply _

#print axioms mutableIndex
#print axioms originals
#print axioms originals_symm_free
#print axioms originals_symm_remaining
#print axioms originals_symm_inverted
#print axioms originals_free
#print axioms originals_remaining
#print axioms originals_inverted
end Verification.FreezingOriginalIndex
