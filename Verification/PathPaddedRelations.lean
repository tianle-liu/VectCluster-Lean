/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathActualKillRelations

/-!
# Path Padded Relations

Deleting the forced endpoint slots recovers exactly the original local
kill and slide predicates from padded coface output words.
-/

namespace Verification.PathPaddedRelations

open Verification.PathWords Verification.PathWordKills Verification.PathFirstBoundary

theorem z_kill_of_padded (w pre tail : List Bool)
    (h : pre++false::true::false::tail=w++[false]) : KilledZ w := by
  have he := congrArg List.dropLast h
  cases tail with
  | nil =>
    simp only [List.dropLast_append_cons,List.dropLast_cons₂,List.dropLast_single,List.dropLast_concat,List.append_nil] at he
    exact ⟨pre,[],Or.inl rfl,he.symm⟩
  | cons a tail =>
    simp only [List.dropLast_append_cons,List.dropLast_cons₂,List.dropLast_concat,List.dropLast_single,List.append_nil] at he
    exact ⟨pre,false::(a::tail).dropLast,Or.inr ⟨_,rfl⟩,he.symm⟩

theorem y_kill_of_padded (w pre tail : List Bool)
    (h : pre++false::true::false::tail=false::(w++[false])) : KilledY w := by
  cases pre with
  | cons a pre => exact Or.inl (z_kill_of_padded w pre tail (List.cons.inj h).2)
  | nil =>
    have he := congrArg List.dropLast (List.cons.inj h).2
    cases tail with
    | nil =>
      simp only [List.dropLast_cons₂,List.dropLast_single,List.dropLast_concat,List.append_nil] at he
      exact Or.inr ⟨[],Or.inl rfl,he.symm⟩
    | cons a tail =>
      simp only [List.dropLast_cons₂,List.dropLast_concat,List.dropLast_single,List.append_nil] at he
      exact Or.inr ⟨false::(a::tail).dropLast,Or.inr ⟨_,rfl⟩,he.symm⟩

theorem z_slide_of_padded {n : ℕ} (u v : Word n) (pre tail : List Bool) (ht : tail ≠ [])
    (hu : pre++true::true::false::tail=u.val++[false])
    (hv : pre++false::true::true::tail=v.val++[false]) : Slide u v := by
  have hU := congrArg List.dropLast hu
  have hV := congrArg List.dropLast hv
  cases tail with
  | nil => exact (ht rfl).elim
  | cons a tail =>
    simp only [List.dropLast_append_cons,List.dropLast_cons₂,List.dropLast_concat,List.dropLast_single,List.append_nil] at hU hV
    exact ⟨pre,(a::tail).dropLast,hU.symm,hV.symm⟩

theorem y_slide_of_padded {n : ℕ} (u v : Word n) (pre tail : List Bool)
    (hp : pre ≠ []) (ht : tail ≠ [])
    (hu : pre++true::true::false::tail=false::(u.val++[false]))
    (hv : pre++false::true::true::tail=false::(v.val++[false])) : Slide u v := by
  cases pre with
  | nil => exact (hp rfl).elim
  | cons a pre => exact z_slide_of_padded u v pre tail ht (List.cons.inj hu).2 (List.cons.inj hv).2

#print axioms z_kill_of_padded
#print axioms y_kill_of_padded
#print axioms z_slide_of_padded
#print axioms y_slide_of_padded

end Verification.PathPaddedRelations
