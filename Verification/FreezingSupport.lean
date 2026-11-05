/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FreezingIndex
import Lean.Elab.Tactic.Omega

/-!
# Freezing Support

The graph partition used in freezing is the support partition of the
actual ordered exchange matrix. Both matrix entries between the removed
vertex and any remaining mutable vertex vanish.
-/
namespace Verification.FreezingSupport
open Verification.FrozenAcyclicCover Verification.FreezingIndex
variable (κ : Type) (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
include hpos hneg hsupport

theorem nonadjacent_entry (i j : Fin n)
    (hij : ¬ ExchangeRing.Adjacent (laterWeights κ n B) i j) :
    B (Sum.inl i) (Sum.inl j) = 0 := by
  have hp : (B (Sum.inl i) (Sum.inl j)).toNat = 0 := by
    by_cases hlt : i < j
    · apply (hsupport i j).mpr
      by_contra h
      exact hij (Or.inl ⟨hlt, h⟩)
    · exact hpos i j hlt
  have hn : (-B (Sum.inl i) (Sum.inl j)).toNat = 0 := by
    by_cases hlt : j < i
    · change laterWeights κ n B j i = 0
      by_contra h
      exact hij (Or.inr ⟨hlt, h⟩)
    · exact hneg i j hlt
  omega

theorem nonadjacent_entry_transpose (i j : Fin n)
    (hij : ¬ ExchangeRing.Adjacent (laterWeights κ n B) i j) :
    B (Sum.inl j) (Sum.inl i) = 0 := by
  apply nonadjacent_entry κ n B hpos hneg hsupport j i
  intro h
  exact hij (h.elim Or.inr Or.inl)

theorem remaining_column (v : Fin n) (i : Remaining κ n B v) :
    B (Sum.inl i.val) (Sum.inl v) = 0 :=
  nonadjacent_entry_transpose κ n B hpos hneg hsupport v i.val i.property.2

theorem remaining_row (v : Fin n) (i : Remaining κ n B v) :
    B (Sum.inl v) (Sum.inl i.val) = 0 :=
  nonadjacent_entry κ n B hpos hneg hsupport v i.val i.property.2

omit hsupport in
theorem diagonal (v : Fin n) : B (Sum.inl v) (Sum.inl v) = 0 := by
  have hp := hpos v v (lt_irrefl v)
  have hn := hneg v v (lt_irrefl v)
  omega

#print axioms nonadjacent_entry
#print axioms nonadjacent_entry_transpose
#print axioms remaining_column
#print axioms remaining_row
#print axioms diagonal
end Verification.FreezingSupport
