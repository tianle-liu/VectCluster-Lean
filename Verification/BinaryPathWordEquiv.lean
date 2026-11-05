/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.BinaryWordCoordinates
import Verification.PathEndpointWordRemoval

/-!
# Binary Path Word Equiv

The genuine recursive torus-word indices are the literal finite lists
used by the path complex. Constant endpoints are padded with false bits;
the existing endpoint projector handles all non-normalized words.
-/
namespace Verification.BinaryPathWordEquiv
open Verification.BinaryWordCoordinates Verification.PathNormalizedBasis
open Verification.PathEndpointWords Verification.PathEndpointWordRemoval

def toList : ∀ n,Index n → List Bool
  | 0,_ => []
  | n+1,(b,i) => b::toList n i

theorem length_toList (n : ℕ) (i : Index n) : (toList n i).length=n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ (ih i.2)

theorem toList_injective (n : ℕ) : Function.Injective (toList n) := by
  induction n with
  | zero => intro a b;cases a;cases b;intro; rfl
  | succ n ih =>
    rintro ⟨a,b⟩ ⟨c,d⟩ h
    have hh:=List.cons.inj h
    exact Prod.ext hh.1 (ih hh.2)

theorem exists_word (n : ℕ) (w : List Bool) (hw : w.length=n) : ∃ i:Index n,toList n i=w := by
  induction n generalizing w with
  | zero =>
    have h : w=[] := List.length_eq_zero_iff.mp hw
    exact ⟨PUnit.unit,h.symm⟩
  | succ n ih =>
    cases w with
    | nil => simp at hw
    | cons a w =>
      obtain ⟨i,hi⟩ := ih w (by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hw)
      exact ⟨(a,i),congrArg (List.cons a) hi⟩

noncomputable def wordEquiv (n : ℕ) : Index n ≃ Verification.PathWords.Word n :=
  Equiv.ofBijective (fun i => ⟨toList n i,length_toList n i⟩)
    ⟨fun _ _ h => toList_injective n (congrArg Subtype.val h),fun w => by
      obtain ⟨i,hi⟩:=exists_word n w.val w.property
      exact ⟨i,Subtype.ext hi⟩⟩

noncomputable def rightEquiv (n : ℕ) : Index n ≃ NormalWord RightNormal (n+1) :=
  (wordEquiv n).trans (rightWordEquiv n).symm

noncomputable def bothEquiv (n : ℕ) : Index n ≃ NormalWord BothNormal (n+2) :=
  (wordEquiv n).trans (bothWordEquiv n).symm

theorem right_val (n : ℕ) (i : Index n) : (rightEquiv n i).val=toList n i++[false] := rfl

theorem both_val (n : ℕ) (i : Index n) : (bothEquiv n i).val=false::(toList n i++[false]) := rfl

#print axioms toList
#print axioms length_toList
#print axioms toList_injective
#print axioms exists_word
#print axioms wordEquiv
#print axioms rightEquiv
#print axioms bothEquiv
#print axioms right_val
#print axioms both_val
end Verification.BinaryPathWordEquiv
