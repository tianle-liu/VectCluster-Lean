/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathConfigRecursion

/-!
# Path Closed Basis Recursion

Actual closed-part path basis recursion, with the Thom cardinality shift
and equality of the compressed free-coordinate word lengths proved.
-/

namespace Verification.PathClosedBasisRecursion

open Classical Verification.PathCompression Verification.PathCochains
  Verification.PathNormalizedBasis Verification.PathFirstVertexSupport
  Verification.PathConfigRecursion

/-- Removing the first zero vertex and its forced neighbor loses exactly one zero. -/
theorem closed_free_count (n : ℕ) (I : ClosedConfig n) :
    (available I.val.val (n+2+2)).card=(available (closedEquiv n I).val (n+2)).card := by
  have ho := available_card I.val.property
  have hn := available_card (closedEquiv n I).property
  have hc := closed_card n I
  omega

/-- The closed-subset indexing retains the literal original word in its fibre. -/
noncomputable def closedRegroup (B : List Bool → Prop) (n : ℕ) :
    ClosedIndex B (n+2) ≃ Σ I : ClosedConfig n, NormalWord B (available I.val.val (n+2+2)).card where
  toFun x := ⟨⟨x.val.1,x.property⟩,x.val.2⟩
  invFun x := ⟨⟨x.1.val,x.2⟩,x.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- All closed basis vectors correspond bijectively to the shorter path, not merely their count. -/
noncomputable def closedIndexEquiv (B : List Bool → Prop) (n : ℕ) :
    ClosedIndex B (n+2) ≃ NormalIndex B n :=
  (closedRegroup B n).trans (Equiv.sigmaCongr (closedEquiv n) (fun I =>
    Equiv.subtypeEquivRight (fun _ => by
      rw [closed_free_count n I])))

theorem closedIndexEquiv_config (B : List Bool → Prop) (n : ℕ) (x : ClosedIndex B (n+2)) :
    (closedIndexEquiv B n x).1=closedEquiv n ⟨x.val.1,x.property⟩ := rfl

theorem closedIndexEquiv_word (B : List Bool → Prop) (n : ℕ) (x : ClosedIndex B (n+2)) :
    (closedIndexEquiv B n x).2.val=x.val.2.val := rfl

theorem closedIndexEquiv_card (B : List Bool → Prop) (n : ℕ) (x : ClosedIndex B (n+2)) :
    (closedIndexEquiv B n x).1.val.card+1=x.val.1.val.card :=
  closed_card n ⟨x.val.1,x.property⟩

#print axioms closed_free_count
#print axioms closedRegroup
#print axioms closedIndexEquiv
#print axioms closedIndexEquiv_config
#print axioms closedIndexEquiv_word
#print axioms closedIndexEquiv_card

end Verification.PathClosedBasisRecursion
