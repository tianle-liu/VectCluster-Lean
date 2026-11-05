/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualFreezingDivisor

/-!
# Freezing Index

The actual mutable vertex partition used for a freezing divisor:
the distinguished vertex, vertices outside its closed neighborhood, and
its neighbors.
-/
noncomputable section
namespace Verification.FreezingIndex
open Verification.FrozenAcyclicCover Verification.ActualFreezingDivisor
variable (κ : Type) (n : ℕ) (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (v : Fin n)

abbrev Remaining := {i : Fin n // i ≠ v ∧ ¬ ExchangeRing.Adjacent (laterWeights κ n B) v i}

def partition {A : Type*} [DecidableEq A] (v : A) (H : A → Prop) (hv : ¬ H v) :
    A ≃ (PUnit ⊕ {i : A // i ≠ v ∧ ¬ H i}) ⊕ {i : A // H i} := by
  classical
  refine {
    toFun := fun i => if h : i = v then Sum.inl (Sum.inl PUnit.unit)
      else if hi : H i then Sum.inr ⟨i, hi⟩ else Sum.inl (Sum.inr ⟨i, h, hi⟩)
    invFun := Sum.elim (Sum.elim (fun _ => v) Subtype.val) Subtype.val
    left_inv := ?_
    right_inv := ?_ }
  · intro i
    dsimp only
    split_ifs with h hi
    · exact h.symm
    · rfl
    · rfl
  · intro i
    rcases i with (u | i) | i
    · cases u
      simp
    · simp [i.property.1, i.property.2]
    · have hi : i.val ≠ v := by
        intro h
        exact hv (h ▸ i.property)
      simp [hi, i.property]

def partners : (Fin n ⊕ Empty) ≃ (PUnit ⊕ Remaining κ n B v) ⊕ Neighbor κ n B v :=
  (Equiv.sumEmpty (Fin n) Empty).trans
    (partition v (ExchangeRing.Adjacent (laterWeights κ n B) v) (by
      simp [ExchangeRing.Adjacent]))

theorem partners_symm_free : (partners κ n B v).symm (Sum.inl (Sum.inl PUnit.unit)) = Sum.inl v := rfl

theorem partners_symm_remaining (i : Remaining κ n B v) :
    (partners κ n B v).symm (Sum.inl (Sum.inr i)) = Sum.inl i.1 := rfl

theorem partners_symm_neighbor (i : Neighbor κ n B v) :
    (partners κ n B v).symm (Sum.inr i) = Sum.inl i.1 := rfl

#print axioms Remaining
#print axioms partition
#print axioms partners
#print axioms partners_symm_free
#print axioms partners_symm_remaining
#print axioms partners_symm_neighbor
end Verification.FreezingIndex
