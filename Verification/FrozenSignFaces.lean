/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FrozenSignStates
import Verification.ActualSignResidue

/-!
# Frozen Sign Faces

The original label extension is precisely the face operation of the
verified state complex, including the frozen signs.
-/
noncomputable section
namespace Verification.FrozenSignFaces
open Verification.SignComplex Verification.FrozenSignStates Verification.SignStateCoordinates
open Verification.AnticliqueSubcolumns Verification.SignFaceAffine Verification.SignFaceRows
variable {V C : Type} [Fintype V] [Fintype C] [DecidableEq V] [LinearOrder (V ⊕ C)]
variable (B : (V ⊕ C) → V → ℤ)

omit [DecidableEq V] in
theorem state_row (I : Finset V) (ε : ActualSignLabels.labels B I) (a : Rows (C := C) I) :
    state B I ε a.val=bitState (ε.val a) := by
  change encode (zeroSet I) (functionsEquiv I ε.val) a.val=_
  have ha : a.val∉zeroSet I := (rowsEquiv I a).property
  simp only [encode,dif_neg ha]
  rfl

omit [DecidableEq V] in
theorem state_hole (I : Finset V) (ε : ActualSignLabels.labels B I) (i : V) (hi : i∈I) :
    state B I ε (Sum.inl i)=none := by
  have h : Sum.inl i∈holes (state B I ε) := by rw [state_holes];simpa using hi
  simpa only [holes,Finset.mem_filter,Finset.mem_univ,true_and] using h

theorem state_extension (I : Finset V) (j : V) (hj : j∉I)
    (hB : ∀ i : I, B (Sum.inl j) i.val=0)
    (ε : ActualSignLabels.labels B (insert j I)) (b : ZMod 2) :
    state B I (labelExtension B I j hj hB ε b)=
      faceState (state B (insert j I) ε) (Sum.inl j) (decide (b=1)) := by
  funext a
  by_cases haj : a=Sum.inl j
  · subst a
    have h := state_row B I (labelExtension B I j hj hB ε b) (oldRow I j hj)
    change state B I (labelExtension B I j hj hB ε b) (Sum.inl j)=_ at h
    rw [h]
    change bitState (extend I j hj (ε.val,b) (oldRow I j hj))=_
    rw [extend_old]
    simp [faceState,bitState]
  · by_cases ha : a∈zeroSet (C := C) I
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp ha
      have haj' : Sum.inl i≠Sum.inl j := haj
      simp only [Function.Embedding.inl_apply]
      rw [state_hole B I _ i hi]
      simp only [faceState,Function.update_of_ne haj']
      exact (state_hole B (insert j I) ε i (Finset.mem_insert_of_mem hi)).symm
    · let ai : Rows (C := C) I := (rowsEquiv I).symm ⟨a,ha⟩
      let aj : Rows (C := C) (insert j I) := addRow I j ai haj
      have hv : aj.val=a := rfl
      have hr : retain I j aj=ai := rfl
      have h₁ := state_row B I (labelExtension B I j hj hB ε b) ai
      have h₂ := state_row B (insert j I) ε aj
      change state B I (labelExtension B I j hj hB ε b) a=_ at h₁
      change state B (insert j I) ε a=_ at h₂
      rw [h₁]
      change bitState (extend I j hj (ε.val,b) ai)=_
      rw [← hr,extend_retain]
      simp only [faceState,Function.update_of_ne haj]
      exact h₂.symm

theorem state_extension_zero (I : Finset V) (j : V) (hj : j∉I)
    (hB : ∀ i : I, B (Sum.inl j) i.val=0) (ε : ActualSignLabels.labels B (insert j I)) :
    state B I (labelExtension B I j hj hB ε 0)=faceState (state B (insert j I) ε) (Sum.inl j) false := by
  simpa using state_extension B I j hj hB ε 0

theorem state_extension_one (I : Finset V) (j : V) (hj : j∉I)
    (hB : ∀ i : I, B (Sum.inl j) i.val=0) (ε : ActualSignLabels.labels B (insert j I)) :
    state B I (labelExtension B I j hj hB ε 1)=faceState (state B (insert j I) ε) (Sum.inl j) true := by
  simpa using state_extension B I j hj hB ε 1

#print axioms state_row
#print axioms state_hole
#print axioms state_extension
#print axioms state_extension_zero
#print axioms state_extension_one
end Verification.FrozenSignFaces
