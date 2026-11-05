/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathPaddedRelations

/-!
# Path Coface Normal Forms

All valid first coface sources split at their original normal position,
and their rho-zero output words satisfy the actual endpoint constraints.
-/

namespace Verification.PathCofaceNormalForms

open Verification.PathEndpointWords Verification.PathNormalWordRecursion
  Verification.PathActualKillRelations Verification.PathEndpointWordRemoval Verification.PathNormalizedBasis

theorem split_at (w : List Bool) (i : ℕ) (hi : i < w.length) :
    ∃ pre bit tail, pre.length=i ∧ w=pre++bit::tail := by
  induction i generalizing w with
  | zero =>
    cases w with
    | nil => simp only [List.length_nil] at hi; omega
    | cons a w => exact ⟨[],a,w,rfl,rfl⟩
  | succ i ih =>
    cases w with
    | nil => simp only [List.length_nil] at hi; omega
    | cons a w =>
      obtain ⟨pre,bit,tail,hp,hw⟩ := ih w (by simp only [List.length_cons] at hi; omega)
      exact ⟨a::pre,bit,tail,by simp only [List.length_cons,hp],by rw [hw]; rfl⟩

theorem right_kill_expand (pre tail : List Bool) (h : RightNormal (pre++false::tail)) :
    RightNormal (pre++false::true::false::tail) := by
  apply (rightNormal_prefix_iff pre (false::true::false::tail) (List.cons_ne_nil _ _)).mpr
  apply (rightNormal_cons false (true::false::tail) (List.cons_ne_nil _ _)).mpr
  apply (rightNormal_cons true (false::tail) (List.cons_ne_nil _ _)).mpr
  exact (rightNormal_prefix_iff pre (false::tail) (List.cons_ne_nil _ _)).mp h

theorem left_kill_expand (pre tail : List Bool) (h : LeftNormal (pre++false::tail)) :
    LeftNormal (pre++false::true::false::tail) := by
  cases pre with
  | nil => rfl
  | cons a pre =>
    have ha : false=a := (List.cons.inj h).1
    rw [← ha]
    rfl

theorem right_slide_expand (pre tail : List Bool) (h : RightNormal (pre++true::tail)) :
    tail ≠ [] ∧ RightNormal (pre++true::true::false::tail) ∧ RightNormal (pre++false::true::true::tail) := by
  have hh := (rightNormal_prefix_iff pre (true::tail) (List.cons_ne_nil _ _)).mp h
  have ht : tail ≠ [] := by
    intro he
    rw [he] at hh
    simp [RightNormal,normalizeRight] at hh
  have htail := (rightNormal_cons true tail ht).mp hh
  refine ⟨ht,?_,?_⟩
  · apply (rightNormal_prefix_iff pre _ (List.cons_ne_nil _ _)).mpr
    apply (rightNormal_cons true _ (List.cons_ne_nil _ _)).mpr
    apply (rightNormal_cons true _ (List.cons_ne_nil _ _)).mpr
    exact (rightNormal_cons false tail ht).mpr htail
  · apply (rightNormal_prefix_iff pre _ (List.cons_ne_nil _ _)).mpr
    apply (rightNormal_cons false _ (List.cons_ne_nil _ _)).mpr
    apply (rightNormal_cons true _ (List.cons_ne_nil _ _)).mpr
    exact (rightNormal_cons true tail ht).mpr htail

theorem left_slide_expand (pre tail : List Bool) (h : LeftNormal (pre++true::tail)) :
    pre ≠ [] ∧ LeftNormal (pre++true::true::false::tail) ∧ LeftNormal (pre++false::true::true::tail) := by
  cases pre with
  | nil => simp [LeftNormal,normalizeLeft] at h
  | cons a pre =>
    have ha : false=a := (List.cons.inj h).1
    rw [← ha]
    exact ⟨List.cons_ne_nil _ _,rfl,rfl⟩

theorem right_padded (n : ℕ) (w : NormalWord RightNormal (n+1)) :
    w.val=(rightWordEquiv n w).val++[false] :=
  (congrArg Subtype.val ((rightWordEquiv n).symm_apply_apply w)).symm

theorem both_padded (n : ℕ) (w : NormalWord BothNormal (n+2)) :
    w.val=false::((bothWordEquiv n w).val++[false]) :=
  (congrArg Subtype.val ((bothWordEquiv n).symm_apply_apply w)).symm

#print axioms split_at
#print axioms right_kill_expand
#print axioms left_kill_expand
#print axioms right_slide_expand
#print axioms left_slide_expand
#print axioms right_padded
#print axioms both_padded

end Verification.PathCofaceNormalForms
