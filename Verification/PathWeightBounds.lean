/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathWeightFiltration

/-!
# Path Weight Bounds

Explicit finite bounds for the actual path weights, before cancellation.
-/

namespace Verification.PathWeightBounds

open Classical Verification.PathCompression Verification.PathCochains
  Verification.PathEndpointWords Verification.PathEndpointTotal
  Verification.PathNormalizedBasis Verification.PathWeightFiltration

theorem right_normal_count (w : List Bool) (hw : RightNormal w) (hn : 0 < w.length) :
    w.count true+1 ≤ w.length := by
  induction w with
  | nil => simp only [List.length_nil] at hn; omega
  | cons a w ih =>
    cases w with
    | nil =>
      have ha : false=a := (List.cons.inj hw).1
      rw [← ha]
      simp
    | cons b tail =>
      have ht : RightNormal (b::tail) := (List.cons.inj hw).2
      have hi := ih ht (by simp)
      cases a with
      | false => simpa using (Nat.le_trans hi (Nat.le_succ _))
      | true => simpa [Nat.add_assoc] using Nat.add_le_add_right hi 1

theorem both_normal_count (w : List Bool) (hw : BothNormal w) (hn : 2 ≤ w.length) :
    w.count true+2 ≤ w.length := by
  cases w with
  | nil => simp only [List.length_nil] at hn; omega
  | cons a w =>
    have ha : false=a := (List.cons.inj hw.1).1
    cases w with
    | nil => simp only [List.length_cons,List.length_nil] at hn; omega
    | cons b tail =>
      have ht : RightNormal (b::tail) := (List.cons.inj hw.2).2
      have hi := right_normal_count (b::tail) ht (by simp)
      rw [← ha]
      simpa [Nat.add_assoc] using Nat.add_le_add_right hi 1

/-- All Z weights lie between zero and n+1, on the actual original basis. -/
theorem z_weight_bound (n : ℕ) (x : NormalIndex RightNormal n) : weight x ≤ n+1 := by
  have hp : 0 < (available x.1.val (n+2)).card :=
    Finset.card_pos.mpr ⟨0,zero_available x.1.property (by omega)⟩
  have hc := available_card x.1.property
  have hl := x.2.property.1
  have hw := right_normal_count x.2.val x.2.property.2 (by omega)
  change x.1.val.card+x.2.val.count true ≤ n+1
  omega

/-- All even Y weights lie between zero and 2a, on its actual quotient basis. -/
theorem y_weight_bound (a : ℕ) (x : NormalIndex BothNormal (2*a)) : weight x ≤ 2*a := by
  have hp := even_free_length a x.1
  have hc := available_card x.1.property
  have hl := x.2.property.1
  have hw := both_normal_count x.2.val x.2.property.2 (by omega)
  change x.1.val.card+x.2.val.count true ≤ 2*a
  omega

#print axioms right_normal_count
#print axioms both_normal_count
#print axioms z_weight_bound
#print axioms y_weight_bound

end Verification.PathWeightBounds
