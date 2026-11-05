/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.Linarith

/-!
# Skew Symmetrizable Signs

The sign symmetry and zero diagonal used by the exchange proofs
follow from an actual positive symmetrizer.
-/
namespace Verification.SkewSymmetrizableSigns
variable {V : Type} (B : V → V → ℤ) (w : V → ℤ)
variable (hw : ∀ i,0<w i) (hB : ∀ a i,w a*B a i=-(w i*B i a))

include hw hB in
theorem sign_iff (a i : V) : 0<B a i ↔ B i a<0 := by
  constructor
  · intro h
    have hp := mul_pos (hw a) h
    rw [hB a i] at hp
    have hn : w i*B i a<0 := by omega
    apply lt_of_not_ge
    intro hz
    exact (not_lt_of_ge (mul_nonneg (le_of_lt (hw i)) hz)) hn
  · intro h
    have hn := mul_neg_of_pos_of_neg (hw i) h
    have hp : 0<w a*B a i := by rw [hB a i];omega
    exact (mul_pos_iff_of_pos_left (hw a)).mp hp

include hw hB in
theorem diagonal (i : V) : B i i=0 := by
  have he := hB i i
  have hn : w i≠0 := ne_of_gt (hw i)
  have hz : w i*B i i=0 := by omega
  exact (mul_eq_zero.mp hz).resolve_left hn

#print axioms sign_iff
#print axioms diagonal
end Verification.SkewSymmetrizableSigns
