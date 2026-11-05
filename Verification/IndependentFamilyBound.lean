/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Powerset

/-!
# Independent Family Bound

The independence number expressed as the maximum cardinality in the
actual independent-set family.
-/
noncomputable section
namespace Verification.IndependentFamilyBound
variable {V : Type} [Fintype V] (F : Finset V → Prop)

def maximum : ℕ := by
  classical
  exact Finset.univ.sup (fun I : Finset V => if F I then I.card else 0)

theorem card_le (I : Finset V) (hI : F I) : I.card≤maximum F := by
  classical
  unfold maximum
  exact Finset.le_sup_of_le (Finset.mem_univ I) (by simp only [hI,if_true,le_refl])

theorem maximum_le_iff (m : ℕ) : maximum F≤m ↔ ∀ I,F I → I.card≤m := by
  classical
  constructor
  · intro h I hI
    exact (card_le F I hI).trans h
  · intro h
    apply Finset.sup_le
    intro I _
    by_cases hI : F I
    · simpa only [hI,if_true] using h I hI
    · simp only [hI,if_false,Nat.zero_le]

#print axioms maximum
#print axioms card_le
#print axioms maximum_le_iff
end Verification.IndependentFamilyBound
