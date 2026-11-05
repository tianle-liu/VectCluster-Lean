/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi

/-!
# Binary Word Coordinates

Finite coefficient coordinates for ordered subset words, split by
whether the first variable occurs.
-/
noncomputable section
namespace Verification.BinaryWordCoordinates

def Index : ℕ → Type
  | 0 => PUnit
  | n+1 => Bool × Index n

instance indexFintype : ∀ n,Fintype (Index n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n+1 => by
    letI := indexFintype n
    exact inferInstanceAs (Fintype (Bool × Index n))

instance indexDecidableEq (n : ℕ) : DecidableEq (Index n) := Classical.decEq _

variable (A : Type*) [AddCommGroup A]

def zeroEquiv : (Index 0 → A) ≃+ A where
  toFun f := f PUnit.unit
  invFun a := fun _ => a
  left_inv f := by funext i; cases i; rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

def succEquiv (n : ℕ) : (Index (n+1) → A) ≃+ (Index n → A) × (Index n → A) where
  toFun f := (fun i => f (false,i),fun i => f (true,i))
  invFun p := fun i => match i.1 with | false => p.1 i.2 | true => p.2 i.2
  left_inv f := by funext i; rcases i with ⟨b,i⟩; cases b <;> rfl
  right_inv p := rfl
  map_add' _ _ := rfl

theorem succ_false (n : ℕ) (i : Index n) (a : A) :
    succEquiv A n (Pi.single (false,i) a)=(Pi.single i a,0) := by
  apply Prod.ext
  · funext j
    by_cases h : j=i
    · subst j; simp [succEquiv]
    · simp only [succEquiv,AddEquiv.coe_mk,Equiv.coe_fn_mk,Pi.single_apply]
      split_ifs with hp
      · exact False.elim (h (congrArg Prod.snd hp))
      · simp [h,Ne.symm h]
  · funext j
    simp only [succEquiv,AddEquiv.coe_mk,Equiv.coe_fn_mk,Pi.single_apply]
    split_ifs with hp
    · have hb := congrArg Prod.fst hp
      cases hb
    · rfl

theorem succ_true (n : ℕ) (i : Index n) (a : A) :
    succEquiv A n (Pi.single (true,i) a)=(0,Pi.single i a) := by
  apply Prod.ext
  · funext j
    simp only [succEquiv,AddEquiv.coe_mk,Equiv.coe_fn_mk,Pi.single_apply]
    split_ifs with hp
    · have hb := congrArg Prod.fst hp
      cases hb
    · rfl
  · funext j
    by_cases h : j=i
    · subst j; simp [succEquiv]
    · simp only [succEquiv,AddEquiv.coe_mk,Equiv.coe_fn_mk,Pi.single_apply]
      split_ifs with hp
      · exact False.elim (h (congrArg Prod.snd hp))
      · simp [h,Ne.symm h]

#print axioms Index
#print axioms indexFintype
#print axioms indexDecidableEq
#print axioms zeroEquiv
#print axioms succEquiv
#print axioms succ_false
#print axioms succ_true
end Verification.BinaryWordCoordinates
