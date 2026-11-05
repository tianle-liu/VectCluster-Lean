/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SignComplex
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

/-!
# Sign State Coordinates

Exact coordinates for states with a prescribed zero set. These connect
the already verified state complex with functions on the sign-label fibers.
-/
noncomputable section
namespace Verification.SignStateCoordinates
open Verification.SignComplex
variable {V : Type*} [Fintype V] [LinearOrder V]

def bitState (x : ZMod 2) : Option Bool := some (decide (x=1))

theorem bitState_value (x : ZMod 2) : signBit (S := ZMod 2) (bitState x)=x := by
  fin_cases x <;> norm_num [bitState,signBit]

theorem bitState_inverse (x : Option Bool) (hx : x≠none) :
    bitState (signBit (S := ZMod 2) x)=x := by
  cases x with
  | none => exact (hx rfl).elim
  | some b => cases b <;> norm_num [bitState,signBit]

def encode (I : Finset V) (ε : {v : V // v∉I} → ZMod 2) : State V :=
  fun v => if h : v∈I then none else bitState (ε ⟨v,h⟩)

theorem encode_holes (I : Finset V) (ε : {v : V // v∉I} → ZMod 2) : holes (encode I ε)=I := by
  ext v
  by_cases hv : v∈I <;> simp [holes,encode,hv,bitState]

def coordinates (I : Finset V) : {s : State V // holes s=I} ≃ ({v : V // v∉I} → ZMod 2) where
  toFun s v := signBit (s.val v.val)
  invFun ε := ⟨encode I ε,encode_holes I ε⟩
  left_inv s := by
    apply Subtype.ext
    funext v
    by_cases hv : v∈I
    · have hs : s.val v=none := by have := hv; rw [← s.property] at this; simpa [holes] using this
      simp [encode,hv,hs]
    · have hs : s.val v≠none := by intro hs; apply hv; rw [← s.property]; simp [holes,hs]
      simp only [encode,dif_neg hv]
      exact bitState_inverse _ hs
  right_inv ε := by
    funext v
    change signBit (encode I ε v.val)=ε v
    simp only [encode,dif_neg v.property]
    exact bitState_value _

theorem character_outside (B : V → V → ZMod 2) (I : Finset V)
    (s : {s : State V // holes s=I}) (i : V) :
    exchangeSignValue B s.val i=∑ a : {v : V // v∉I}, B a.val i * coordinates I s a := by
  change (∑ a, B a i*signBit (s.val a))=_
  rw [← (Equiv.sumCompl (fun v => v∈I)).sum_comp (fun a => B a i*signBit (s.val a)),Fintype.sum_sum_type]
  have hz : (∑ a : {v : V // v∈I}, B a.val i*signBit (s.val a.val))=0 := by
    apply Finset.sum_eq_zero
    intro a _
    have hs : s.val a.val=none := by
      have h : a.val∈holes s.val := by simpa only [s.property] using a.property
      simpa [holes] using h
    simp [hs,signBit]
  change (∑ a : {v : V // v∈I}, B a.val i*signBit (s.val a.val))+
    (∑ a : {v : V // v∉I}, B a.val i*signBit (s.val a.val))=_
  rw [hz,zero_add]
  rfl

def fiberCoordinates (B : V → V → ZMod 2) (I : Finset V) :
    {s : {s : State V // holes s=I} // ∀ i : I, exchangeSignValue B s.val i.val=1} ≃
      {ε : {v : V // v∉I} → ZMod 2 // ∀ i : I, ∑ a, B a.val i.val*ε a=1} := by
  apply Equiv.subtypeEquiv (coordinates I)
  intro s
  simp only [character_outside]

#print axioms bitState
#print axioms bitState_value
#print axioms bitState_inverse
#print axioms encode
#print axioms encode_holes
#print axioms coordinates
#print axioms character_outside
#print axioms fiberCoordinates
end Verification.SignStateCoordinates
