/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.BinaryWordCoordinates
import Verification.GradedSectionTotal

/-!
# Graded Binary Coefficient Tree

Degree-shifted coefficient trees for iterated Laurent splitting. Each
chosen parameter lowers the coefficient degree by exactly one.
-/
noncomputable section
namespace Verification.GradedBinaryCoefficientTree
open Verification.BinaryWordCoordinates Verification.GradedSectionTotal
open scoped DirectSum
variable (G : ℤ → Type*)

def Tree : ℕ → ℤ → Type _
  | 0,q => G q
  | n+1,q => Tree n q × Tree n (q-1)

instance treeAddCommGroup [∀ q,AddCommGroup (G q)] : ∀ n q,AddCommGroup (Tree G n q)
  | 0,q => inferInstanceAs (AddCommGroup (G q))
  | n+1,q => by
    letI := treeAddCommGroup n q
    letI := treeAddCommGroup n (q-1)
    exact inferInstanceAs (AddCommGroup (Tree G n q × Tree G n (q-1)))

variable [∀ q,AddCommGroup (G q)] {A : Type*} [AddCommGroup A]
variable (E : (⨁ q,G q) ≃+ A)

def embed : ∀ n q,Tree G n q →+ (Index n → A)
  | 0,q => {
      toFun := fun a _ => includeDegree E q a
      map_zero' := by funext i; exact map_zero _
      map_add' := by intro a b; funext i; exact map_add _ a b }
  | n+1,q => {
      toFun := fun a i => match i with
        | (false,k) => embed n q a.1 k
        | (true,k) => embed n (q-1) a.2 k
      map_zero' := by
        funext i; rcases i with ⟨b,k⟩; cases b
        · exact congrArg (fun f=>f k) (map_zero (embed n q))
        · exact congrArg (fun f=>f k) (map_zero (embed n (q-1)))
      map_add' := by
        intro a b; funext i; rcases i with ⟨c,k⟩; cases c
        · exact congrArg (fun f=>f k) (map_add (embed n q) a.1 b.1)
        · exact congrArg (fun f=>f k) (map_add (embed n (q-1)) a.2 b.2) }

theorem embed_injective (n : ℕ) (q : ℤ) : Function.Injective (embed G E n q) := by
  induction n generalizing q with
  | zero =>
    intro a b h
    exact includeDegree_injective E q (congrArg (fun f=>f PUnit.unit) h)
  | succ n ih =>
    intro a b h
    apply Prod.ext
    · apply ih q
      funext i
      exact congrArg (fun f=>f (false,i)) h
    · apply ih (q-1)
      funext i
      exact congrArg (fun f=>f (true,i)) h

def weight : ∀ n,Index n → ℤ
  | 0,_ => 0
  | n+1,(false,i) => weight n i
  | n+1,(true,i) => 1+weight n i

theorem embed_degree (n : ℕ) (q : ℤ) (a : Tree G n q) (i : Index n) :
    ∃ b : G (q-weight n i),includeDegree E (q-weight n i) b=embed G E n q a i := by
  induction n generalizing q with
  | zero =>
    change ∃ b : G (q-0),includeDegree E (q-0) b=embed G E 0 q a i
    rw [sub_zero]
    exact ⟨a,rfl⟩
  | succ n ih =>
    rcases i with ⟨b,i⟩
    cases b
    · exact ih q a.1 i
    · have h := ih (q-1) a.2 i
      have he : (q-1)-weight n i=q-(1+weight n i) := by omega
      change ∃ b : G (q-(1+weight n i)),includeDegree E (q-(1+weight n i)) b=embed G E n (q-1) a.2 i
      rw [← he]
      exact h

#print axioms Tree
#print axioms treeAddCommGroup
#print axioms embed
#print axioms embed_injective
#print axioms weight
#print axioms embed_degree
end Verification.GradedBinaryCoefficientTree
