/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathWordKills

/-!
# Path Word Normal Form

Canonical representatives of all surviving binary-word components.
-/

namespace Verification.PathWordNormalForm

open Verification.Path Verification.PathWords Verification.PathWordSlides Verification.PathWordKills

theorem parities_even (r : List ℕ) (h : ∀ a ∈ r, a % 2 = 0) :
    parities r = List.replicate r.length 0 := by
  induction r with
  | nil => rfl
  | cons a tail ih =>
    simp only [parities, List.map_cons, List.length_cons, List.replicate_succ]
    rw [h a (by simp), show tail.map (· % 2) = List.replicate tail.length 0 from
      ih (fun b hb => h b (by simp [hb]))]

theorem sum_even (r : List ℕ) (h : ∀ a ∈ r, a % 2 = 0) : r.sum % 2 = 0 := by
  induction r with
  | nil => rfl
  | cons a tail ih =>
    rw [List.sum_cons, Nat.add_mod, h a (by simp), ih (fun b hb => h b (by simp [hb]))]

theorem parities_tail_even (r : List ℕ) (hr : r ≠ [])
    (h : ∀ a ∈ r.tail, a % 2 = 0) :
    parities r = (r.sum % 2) :: List.replicate (r.length-1) 0 := by
  cases r with
  | nil => contradiction
  | cons a tail =>
    change ∀ b ∈ tail, b % 2 = 0 at h
    have hs := sum_even tail h
    simpa only [parities, List.map_cons, List.sum_cons, Nat.add_mod, hs,
      Nat.add_zero, Nat.mod_mod, List.length_cons, Nat.add_sub_cancel] using
      congrArg (List.cons (a % 2)) (parities_even tail h)

/-- The normalized survivor of weight k, as an actual binary word. -/
def normal (n k : ℕ) : List Bool := List.replicate k true ++ List.replicate (n-k) false

theorem normal_length (n k : ℕ) (h : k ≤ n) : (normal n k).length = n := by
  simp only [normal, List.length_append, List.length_replicate]
  omega

theorem normal_weight (n k : ℕ) : (normal n k).count true = k := by
  simp [normal, List.count_eq_zero]

theorem runs_false (n : ℕ) : runs (List.replicate n false) = List.replicate (n+1) 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, runs, ih]

theorem runs_normal (n k : ℕ) : runs (normal n k) = k :: List.replicate (n-k) 0 := by
  have hh : runs (List.replicate (n-k) false) = 0 :: List.replicate (n-k) 0 := by
    rw [runs_false, List.replicate_succ]
  simpa only [normal, Nat.zero_add] using
    runs_replicate_append k 0 (List.replicate (n-k) 0) _ hh

theorem normal_goodZ (n k : ℕ) : GoodZ (normal n k) := by
  intro a ha
  rw [runs_normal] at ha
  simp only [List.tail_cons, List.mem_replicate] at ha
  simp [ha.2]

theorem normal_goodY (n k : ℕ) (h : k % 2 = 0) : GoodY (normal n k) := by
  intro a ha
  rw [runs_normal] at ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact h
  · simp only [List.mem_replicate] at ha
    simp [ha.2]

theorem goodY_goodZ {w : List Bool} (h : GoodY w) : GoodZ w :=
  fun a ha => h a (List.mem_of_mem_tail ha)

theorem goodY_weight_even {w : List Bool} (h : GoodY w) : w.count true % 2 = 0 := by
  rw [← runs_sum]
  exact sum_even _ h

/-- At fixed length and weight all allowed Z words lie in one literal slide component. -/
theorem goodZ_connected {u v : List Bool} (hu : GoodZ u) (hv : GoodZ v)
    (hn : u.length = v.length) (hk : u.count true = v.count true) : WordConnected u v := by
  apply (wordConnected_iff u v).mpr
  refine ⟨?_, hk⟩
  rw [parities_tail_even _ (runs_ne_nil u) hu, parities_tail_even _ (runs_ne_nil v) hv,
    runs_sum, runs_sum, hk]
  have hl : (runs u).length = (runs v).length := by
    have h₁ := runs_length_weight u
    have h₂ := runs_length_weight v
    rw [runs_sum] at h₁ h₂
    omega
  rw [hl]

/-- Every surviving original word is connected to the explicit left-packed representative. -/
theorem goodZ_normal (w : List Bool) (h : GoodZ w) :
    WordConnected w (normal w.length (w.count true)) := by
  apply goodZ_connected h (normal_goodZ _ _)
  · exact (normal_length _ _ List.count_le_length).symm
  · exact (normal_weight _ _).symm

/-- Goodness is a true invariant of the slide equivalence relation. -/
theorem goodY_iff_of_connected {u v : List Bool} (h : WordConnected u v) : GoodY u ↔ GoodY v := by
  have hp := (wordConnected_iff u v).mp h |>.1
  have aux : ∀ w : List Bool, GoodY w ↔ ∀ a ∈ parities (runs w), a = 0 := by
    intro w
    simp only [GoodY, parities, List.mem_map, forall_exists_index, and_imp]
    constructor
    · intro hg a b hb he
      simpa only [← he] using hg b hb
    · intro hg a ha
      exact hg (a % 2) a ha rfl
  rw [aux, aux, hp]

theorem goodZ_iff_of_connected {u v : List Bool} (h : WordConnected u v) : GoodZ u ↔ GoodZ v := by
  have hp := (wordConnected_iff u v).mp h |>.1
  have ht : parities (runs u).tail = parities (runs v).tail := by
    simpa only [parities, List.map_tail] using congrArg List.tail hp
  have aux : ∀ w : List Bool, GoodZ w ↔ ∀ a ∈ parities (runs w).tail, a = 0 := by
    intro w
    simp only [GoodZ, parities, List.mem_map, forall_exists_index, and_imp]
    constructor
    · intro hg a b hb he
      simpa only [← he] using hg b hb
    · intro hg a ha
      exact hg (a % 2) a ha rfl
  rw [aux, aux, ht]

#print axioms parities_even
#print axioms sum_even
#print axioms parities_tail_even
#print axioms normal
#print axioms normal_length
#print axioms normal_weight
#print axioms runs_false
#print axioms runs_normal
#print axioms normal_goodZ
#print axioms normal_goodY
#print axioms goodY_goodZ
#print axioms goodY_weight_even
#print axioms goodZ_connected
#print axioms goodZ_normal
#print axioms goodY_iff_of_connected
#print axioms goodZ_iff_of_connected

end Verification.PathWordNormalForm
