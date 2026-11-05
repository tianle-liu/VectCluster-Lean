/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathWordSlides

/-!
# Path Word Kills

The other original first-boundary relations: a selected mutable position
with vacant neighbors is killed. The initial position is frozen in Z, so only
Y permits the initial singleton relation.
-/

namespace Verification.PathWordKills

open Verification.Path Verification.PathWords Verification.PathWordSlides

/-- The selected position has no selected right neighbor. -/
def RightVacant (post : List Bool) : Prop := post=[] ∨ ∃ tail, post=false :: tail

/-- An isolated selected mutable position after an actual vacancy. -/
def KilledZ (w : List Bool) : Prop :=
  ∃ pre post, RightVacant post ∧ w=pre ++ false :: true :: post

/-- Y also has a mutable first position; these are precisely the endpoint relations. -/
def KilledY (w : List Bool) : Prop := KilledZ w ∨
  ∃ post, RightVacant post ∧ w=true :: post

/-- All runs have even parity in a surviving Y component. -/
def GoodY (w : List Bool) : Prop := ∀ a ∈ runs w, a % 2=0

/-- Only the initial, frozen run may have odd parity in Z. -/
def GoodZ (w : List Bool) : Prop := ∀ a ∈ (runs w).tail, a % 2=0

theorem tail_one_prefix (pre w : List Bool) (h : 1 ∈ (runs w).tail) :
    1 ∈ (runs (pre ++ w)).tail := by
  induction pre with
  | nil => exact h
  | cons b pre ih =>
    cases b
    · exact List.mem_of_mem_tail ih
    · cases hr : runs (pre ++ w) with
      | nil => exact (runs_ne_nil _ hr).elim
      | cons a tail => simpa only [List.cons_append,runs,hr,addHead,List.tail_cons] using ih

theorem killedZ_one (w : List Bool) (h : KilledZ w) : 1 ∈ (runs w).tail := by
  obtain ⟨pre,post,hpost,rfl⟩ := h
  apply tail_one_prefix
  rcases hpost with rfl | ⟨tail,rfl⟩ <;> simp [runs,addHead]

theorem killedY_one (w : List Bool) (h : KilledY w) : 1 ∈ runs w := by
  rcases h with h | ⟨post,hpost,rfl⟩
  · exact List.mem_of_mem_tail (killedZ_one w h)
  · rcases hpost with rfl | ⟨tail,rfl⟩ <;> simp [runs,addHead]

theorem killedZ_not_good (w : List Bool) (h : KilledZ w) : ¬GoodZ w := by
  intro hg
  have hh := hg 1 (killedZ_one w h)
  omega

theorem killedY_not_good (w : List Bool) (h : KilledY w) : ¬GoodY w := by
  intro hg
  have hh := hg 1 (killedY_one w h)
  omega

/-- Concatenating run vectors inserts exactly the separating vacancy. -/
theorem encode_append (r s : List ℕ) (hr : r ≠ []) (hs : s ≠ []) :
    encode (r ++ s)=encode r ++ false :: encode s := by
  induction r with
  | nil => exact (hr rfl).elim
  | cons a r ih =>
    cases r with
    | nil =>
      cases s with
      | nil => exact (hs rfl).elim
      | cons b s => simp [encode]
    | cons b r =>
      change List.replicate a true ++ false :: encode ((b :: r) ++ s)=
        (List.replicate a true ++ false :: encode (b :: r)) ++ false :: encode s
      rw [ih (by simp)]
      simp only [List.append_assoc,List.cons_append]

/-- A singleton noninitial run is a literal mutable singleton relation. -/
theorem encode_tail_one (r : List ℕ) (h : 1 ∈ r.tail) : KilledZ (encode r) := by
  cases r with
  | nil => simp at h
  | cons a r =>
    change 1 ∈ r at h
    obtain ⟨pre,post,hp⟩ := List.append_of_mem h
    rw [hp]
    have he : encode ((a :: pre) ++ 1 :: post)=encode (a :: pre) ++ false :: encode (1 :: post) :=
      encode_append (a :: pre) (1 :: post) (by simp) (by simp)
    change KilledZ (encode ((a :: pre) ++ 1 :: post))
    rw [he]
    cases post with
    | nil => exact ⟨encode (a :: pre),[],Or.inl rfl,by simp [encode]⟩
    | cons b post =>
      exact ⟨encode (a :: pre),false :: encode (b :: post),Or.inr ⟨_,rfl⟩,by simp [encode]⟩

/-- An initial singleton is also mutable in Y. -/
theorem encode_head_one (tail : List ℕ) : KilledY (encode (1 :: tail)) := by
  right
  cases tail with
  | nil => exact ⟨[],Or.inl rfl,by simp [encode]⟩
  | cons b tail => exact ⟨false :: encode (b :: tail),Or.inr ⟨_,rfl⟩,by simp [encode]⟩

/-- Every disallowed Z parity component contains a literal killed monomial. -/
theorem badZ_killed (w : List Bool) (hbad : ¬GoodZ w) :
    ∃ v, WordConnected w v ∧ KilledZ v := by
  classical
  have hbad' : ∃ a ∈ (runs w).tail, a % 2 ≠ 0 := by
    unfold GoodZ at hbad
    push_neg at hbad
    exact hbad
  obtain ⟨a,ha,hodd⟩ := hbad'
  have haodd : a % 2=1 := by omega
  cases hr : runs w with
  | nil => exact (runs_ne_nil w hr).elim
  | cons b tail =>
    let r := packPairs (parities (b :: tail)) (pairCount (b :: tail))
    refine ⟨encode r,?_,?_⟩
    · have hc := encode_runConnected (connected_normal_form (runs w))
      have hw : encode (b :: tail)=w := by rw [←hr,encode_runs]
      simpa only [hr,hw] using hc
    · apply encode_tail_one
      change 1 ∈ parities tail
      apply List.mem_map.mpr
      exact ⟨a,by simpa only [hr,List.tail_cons] using ha,haodd⟩

/-- Every disallowed Y component contains a killed monomial; even path length
is used exactly to exclude the fully selected odd word. -/
theorem badY_killed (w : List Bool) (heven : w.length % 2=0) (hbad : ¬GoodY w) :
    ∃ v, WordConnected w v ∧ KilledY v := by
  classical
  by_cases hz : GoodZ w
  · have hbad' : ∃ a ∈ runs w, a % 2 ≠ 0 := by
      unfold GoodY at hbad
      push_neg at hbad
      exact hbad
    obtain ⟨a,ha,hodd⟩ := hbad'
    cases hr : runs w with
    | nil => exact (runs_ne_nil w hr).elim
    | cons b tail =>
      have he : a=b := by
        rcases List.mem_cons.mp (hr ▸ ha) with h | h
        · exact h
        · exact (hodd (hz a (by simpa only [hr,List.tail_cons] using h))).elim
      subst a
      have hb : b % 2=1 := by omega
      cases tail with
      | nil =>
        have hl := runs_length_weight w
        simp only [hr,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil] at hl
        omega
      | cons c tail =>
        let r := 1 :: (c+2*(b/2)) :: tail
        refine ⟨encode r,?_,encode_head_one _⟩
        have hc := encode_runConnected (odd_run_to_singleton_right [] tail b c hb)
        simpa only [List.nil_append,←hr,encode_runs] using hc
  · obtain ⟨v,hv,hk⟩ := badZ_killed w hz
    exact ⟨v,hv,Or.inl hk⟩

#print axioms RightVacant
#print axioms KilledZ
#print axioms KilledY
#print axioms GoodY
#print axioms GoodZ
#print axioms tail_one_prefix
#print axioms killedZ_one
#print axioms killedY_one
#print axioms killedZ_not_good
#print axioms killedY_not_good
#print axioms encode_append
#print axioms encode_tail_one
#print axioms encode_head_one
#print axioms badZ_killed
#print axioms badY_killed

end Verification.PathWordKills
