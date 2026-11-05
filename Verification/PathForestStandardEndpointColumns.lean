/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathForestFrozenBasis
import Verification.PathForestComponentPresentation

/-!
# Path Forest Standard Endpoint Columns

The standard frozen rows of the actual normalized forest become exactly
one endpoint column per odd path under the genuine consecutive reindexing.
-/
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 600000
namespace Verification.PathForestStandardEndpointColumns
open Classical Verification.PathForestMatching Verification.PathForestQuotient
open Verification.PathForestComponentMatrix Verification.PathForestFrozenBasis

theorem local_endpoint (m : ℕ) (o : Bool) (z : ℤ)
    (i : Fin (PathOrientationBlocks.length m o)) :
    Sum.elim (localEndpoint m o z).1 (localEndpoint m o z).2
      ((PathOrientationBlocks.reindex m o).symm i)=
        if i.val=0 then (if o then z else 0) else 0 := by
  obtain ⟨i,rfl⟩ := (PathOrientationBlocks.reindex m o).surjective i
  rw [Equiv.symm_apply_apply]
  cases o with
  | false => simp [localEndpoint]
  | true =>
    cases i with
    | inl i =>
      change (Pi.single (⟨0,by omega⟩ : Fin (m+1)) z : Fin (m+1) → ℤ) i=if 2*i.val=0 then z else 0
      by_cases hi : i=(⟨0,by omega⟩ : Fin (m+1))
      · subst i
        rw [Pi.single_eq_same]
        rfl
      · rw [Pi.single_eq_of_ne hi]
        have hn : 2*i.val≠0 := by
          intro h
          apply hi
          apply Fin.ext
          change i.val=0
          omega
        rw [if_neg hn]
    | inr i =>
      change (0:ℤ)=if 2*i.val+1=0 then z else 0
      simp

variable {S F : Type} [Fintype S] [Fintype F] (m : S → ℕ) (o : S → Bool)

omit [Fintype S] in
theorem endpoint_consecutive (x : Odd o → ℤ)
    (v : PathForestOrientation.Vertex m o) :
    endpoint m o x ((PathForestOrientation.reindex m o).symm v)=
      if v.2.val=0 then oddValue o x v.1 else 0 := by
  obtain ⟨v,rfl⟩ := (PathForestOrientation.reindex m o).surjective v
  rw [Equiv.symm_apply_apply]
  rcases v with ⟨s,i⟩ | ⟨s,i⟩
  all_goals
    have h := local_endpoint (m s) (o s) (oddValue o x s)
  · specialize h (PathOrientationBlocks.reindex (m s) (o s) (Sum.inl i))
    rw [Equiv.symm_apply_apply] at h
    change (localEndpoint (m s) (o s) (oddValue o x s)).1 i=_ at h
    change (localEndpoint (m s) (o s) (oddValue o x s)).1 i=_
    rw [h]
    by_cases ho : o s=true
    · simp [PathForestOrientation.reindex,PathForestOrientation.sides,Sigma.map,ho]
    · simp [PathForestOrientation.reindex,PathForestOrientation.sides,Sigma.map,oddValue,ho]
  · specialize h (PathOrientationBlocks.reindex (m s) (o s) (Sum.inr i))
    rw [Equiv.symm_apply_apply] at h
    change (localEndpoint (m s) (o s) (oddValue o x s)).2 i=_ at h
    change (localEndpoint (m s) (o s) (oddValue o x s)).2 i=_
    rw [h]
    by_cases ho : o s=true
    · simp [PathForestOrientation.reindex,PathForestOrientation.sides,Sigma.map,ho]
    · simp [PathForestOrientation.reindex,PathForestOrientation.sides,Sigma.map,oddValue,ho]

theorem odd_row (a : Odd o) (v : PathForestOrientation.Vertex m o) :
    standardFrozen (F:=F) m o (Sum.inl a)
        ((PathForestOrientation.reindex m o).symm v)=
      if a.val=v.1 ∧ v.2.val=0 then (1:ℤ) else 0 := by
  simp only [standardFrozen,FrozenQuotientCoordinates.standardRow,Sum.elim_inl]
  rw [endpoint_consecutive]
  by_cases h : a.val=v.1
  · rcases v with ⟨s,i⟩
    change a.val=s at h
    subst s
    simp [oddValue,a.property]
  · have hn : ∀ hv : o v.1=true, (⟨v.1,hv⟩ : Odd o)≠a := by
      intro hv he
      exact h (congrArg Subtype.val he).symm
    simp [oddValue,h,hn]

theorem unused_row (a : Fin (Fintype.card F-Fintype.card (Odd o)))
    (v : PathForestOrientation.Vertex m o) :
    standardFrozen (F:=F) m o (Sum.inr a)
      ((PathForestOrientation.reindex m o).symm v)=0 := by
  rw [standard_unused]
  rfl

#print axioms local_endpoint
#print axioms endpoint_consecutive
#print axioms odd_row
#print axioms unused_row
end Verification.PathForestStandardEndpointColumns
