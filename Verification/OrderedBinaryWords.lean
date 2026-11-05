/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.BinaryWordCoordinates

/-!
# Ordered Binary Words

Ordered subset products indexed by the binary coefficient coordinates.
-/
namespace Verification.OrderedBinaryWords
open Verification.BinaryWordCoordinates
variable {A B : Type*} [Monoid A] [Monoid B]

def word : ∀ n,(Fin n → A) → Index n → A
  | 0,_,_ => 1
  | n+1,x,(false,i) => word n (fun k => x k.succ) i
  | n+1,x,(true,i) => x 0*word n (fun k => x k.succ) i

theorem map_word (F : A →* B) (n : ℕ) (x : Fin n → A) (i : Index n) :
    F (word n x i)=word n (fun k => F (x k)) i := by
  induction n with
  | zero => exact map_one F
  | succ n ih =>
    rcases i with ⟨b,i⟩
    cases b
    · exact ih (fun k => x k.succ) i
    · exact (map_mul F _ _).trans (congrArg (fun y => F (x 0)*y) (ih (fun k=>x k.succ) i))

#print axioms word
#print axioms map_word
end Verification.OrderedBinaryWords
