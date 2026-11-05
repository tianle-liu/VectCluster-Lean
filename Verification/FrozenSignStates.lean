/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SignStateCoordinates
import Verification.ActualSignLabels
import Mathlib.Data.Sum.Order

/-!
# Frozen Sign States

Sign labels with all frozen coordinates retained, expressed as states
whose holes are exactly the selected mutable coordinates.
-/
noncomputable section
namespace Verification.FrozenSignStates
open Verification.SignComplex Verification.AnticliqueSubcolumns
variable {V C : Type} [Fintype V] [Fintype C] [LinearOrder (V ⊕ C)]

def zeroSet (I : Finset V) : Finset (V ⊕ C) := I.map Function.Embedding.inl

omit [Fintype V] [Fintype C] [LinearOrder (V ⊕ C)] in
@[simp] theorem inl_mem_zeroSet (I : Finset V) (v : V) : Sum.inl v∈zeroSet (C := C) I ↔ v∈I := by
  simp [zeroSet]

omit [Fintype V] [Fintype C] [LinearOrder (V ⊕ C)] in
@[simp] theorem inr_not_mem_zeroSet (I : Finset V) (c : C) : Sum.inr c∉zeroSet I := by
  simp [zeroSet]

omit [Fintype V] [Fintype C] [LinearOrder (V ⊕ C)] in
theorem zeroSet_injective : Function.Injective (zeroSet (V := V) (C := C)) := by
  intro I J h
  ext v
  have := Finset.ext_iff.mp h (Sum.inl v)
  simpa using this

def rowsEquiv (I : Finset V) : Rows (C := C) I ≃ {a : V ⊕ C // a∉zeroSet I} := by
  refine Equiv.subtypeEquiv (Equiv.refl _) ?_
  intro a
  simp only [Equiv.refl_apply,zeroSet,Finset.mem_map,Function.Embedding.inl_apply,not_exists,not_and]
  constructor
  · intro h v hv he
    exact h v hv he.symm
  · intro h v hv he
    exact h v hv he.symm

def functionsEquiv (I : Finset V) :
    (Rows (C := C) I → ZMod 2) ≃ ({a : V ⊕ C // a∉zeroSet I} → ZMod 2) :=
  Equiv.piCongrLeft' (fun _ => ZMod 2) (rowsEquiv I)

def matrix (B : (V ⊕ C) → V → ℤ) : (V ⊕ C) → (V ⊕ C) → ZMod 2 :=
  fun a i => i.elim (fun i => (B a i : ZMod 2)) (fun _ => 0)

theorem character_reindex (B : (V ⊕ C) → V → ℤ) (I : Finset V)
    (ε : Rows (C := C) I → ZMod 2) (i : V) :
    (∑ a : Rows (C := C) I, (B a.val i:ZMod 2)*ε a)=
      ∑ a : {a : V ⊕ C // a∉zeroSet I}, matrix B a.val (Sum.inl i)*functionsEquiv I ε a := by
  rw [← (rowsEquiv I).symm.sum_comp (fun a => (B a.val i:ZMod 2)*ε a)]
  rfl

def labelsEquiv (B : (V ⊕ C) → V → ℤ) (I : Finset V) :
    ActualSignLabels.labels B I ≃
      {ε : {a : V ⊕ C // a∉zeroSet I} → ZMod 2 //
        ∀ i : zeroSet (C := C) I, ∑ a, matrix B a.val i.val*ε a=1} := by
  apply Equiv.subtypeEquiv (functionsEquiv I)
  intro ε
  constructor
  · intro h i
    rcases i with ⟨i,hi⟩
    cases i with
    | inl i => exact (character_reindex B I ε i).symm.trans (h ⟨i,by simpa using hi⟩)
    | inr c => exact (inr_not_mem_zeroSet I c hi).elim
  · intro h i
    exact (character_reindex B I ε i.val).trans (h ⟨Sum.inl i.val,by simp [i.property]⟩)

def coordinates (B : (V ⊕ C) → V → ℤ) (I : Finset V) :
    {s : {s : State (V ⊕ C) // holes s=zeroSet I} //
      ∀ i : zeroSet (C := C) I, exchangeSignValue (matrix B) s.val i.val=1} ≃
      ActualSignLabels.labels B I :=
  (SignStateCoordinates.fiberCoordinates (matrix B) (zeroSet I)).trans (labelsEquiv B I).symm

def state (B : (V ⊕ C) → V → ℤ) (I : Finset V) (ε : ActualSignLabels.labels B I) : State (V ⊕ C) :=
  ((coordinates B I).symm ε).val.val

theorem state_holes (B : (V ⊕ C) → V → ℤ) (I : Finset V) (ε : ActualSignLabels.labels B I) :
    holes (state B I ε)=zeroSet I := ((coordinates B I).symm ε).val.property

theorem state_equations (B : (V ⊕ C) → V → ℤ) (I : Finset V)
    (ε : ActualSignLabels.labels B I) (i : zeroSet (C := C) I) :
    exchangeSignValue (matrix B) (state B I ε) i.val=1 := ((coordinates B I).symm ε).property i

#print axioms zeroSet
#print axioms inl_mem_zeroSet
#print axioms inr_not_mem_zeroSet
#print axioms zeroSet_injective
#print axioms rowsEquiv
#print axioms functionsEquiv
#print axioms matrix
#print axioms character_reindex
#print axioms labelsEquiv
#print axioms coordinates
#print axioms state
#print axioms state_holes
#print axioms state_equations
end Verification.FrozenSignStates
