/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FrozenSignDifferential

/-!
# Frozen Sign Intertwiner

The whole literal label differential is intertwined with the verified
state differential. Consequently its square vanishes without an assumed relation.
-/
noncomputable section
namespace Verification.FrozenSignIntertwiner
open Verification.FrozenSignTerms Verification.FrozenSignIncidence Verification.FrozenSignDifferential
open Verification.FrozenSignStates Verification.FrozenSignFamily Verification.SignComplex
variable {V C : Type} [Fintype V] [Fintype C] [DecidableEq V] [LinearOrder (V ⊕ C)]
variable (B : (V ⊕ C) → V → ℤ) (F : Finset V → Prop)
variable (down : ∀ I J, J⊆I → F I → F J)
variable (indep : ∀ I, F I → ∀ i∈I, ∀ j∈I, i≠j → B (Sum.inl j) i=0)

theorem face_evaluation (p : ℕ) (f : SignHomology.term (allowed B F) p)
    (J : Index F (p+1)) (j : J.val) (ε : ActualSignLabels.labels B J.val) :
    faceMap B F down indep p J j (termCoordinates B F p f) ε=
      extendCochain (allowed B F) f.val (faceState (state B J.val ε) (Sum.inl j.val) false)-
      extendCochain (allowed B F) f.val (faceState (state B J.val ε) (Sum.inl j.val) true) := by
  let I := sourceIndex F down p J j
  let hB := face_zero B F indep p J j
  let e := extension B I.val J.val j.val (Finset.not_mem_erase _ _) (Finset.insert_erase j.property) hB ε
  have h0 : state B I.val (e 0)=faceState (state B J.val ε) (Sum.inl j.val) false := by
    simpa only [show decide ((0:ZMod 2)=1)=false by decide] using
      extension_state B I.val J.val j.val (Finset.not_mem_erase _ _) (Finset.insert_erase j.property) hB ε 0
  have h1 : state B I.val (e 1)=faceState (state B J.val ε) (Sum.inl j.val) true := by
    simpa only [decide_true] using
      extension_state B I.val J.val j.val (Finset.not_mem_erase _ _) (Finset.insert_erase j.property) hB ε 1
  change termCoordinates B F p f ⟨I,e 0⟩-termCoordinates B F p f ⟨I,e 1⟩=_
  rw [termCoordinates_apply,termCoordinates_apply,← h0,← h1]
  rw [extendCochain_apply _ _ _ (state_allowed B F I.val I.property.1 (e 0)),
    extendCochain_apply _ _ _ (state_allowed B F I.val I.property.1 (e 1))]

theorem intertwines (p : ℕ) (f : SignHomology.term (allowed B F) p) :
    termCoordinates B F (p+1) (degreeDifferential (allowed B F) p f)=
      FrozenSignDifferential.differential B F down indep p (termCoordinates B F p f) := by
  funext q
  rw [termCoordinates_apply,differential_apply]
  change SignComplex.differential (extendCochain (allowed B F) f.val) (state B q.1.val q.2)=_
  rw [differential_eq_sum_holes,state_holes]
  simp only [zeroSet,Finset.sum_map,Function.Embedding.inl_apply]
  rw [← Finset.sum_coe_sort q.1.val]
  apply Finset.sum_congr rfl
  intro j _
  rw [state_incidence,face_evaluation B F down indep p f q.1 j q.2]

theorem differential_squared (p : ℕ) (f : Labels B F p → ℤ) :
    FrozenSignDifferential.differential B F down indep (p+1)
      (FrozenSignDifferential.differential B F down indep p f)=0 := by
  let a := (termCoordinates B F p).symm f
  have h1 : termCoordinates B F (p+1) (degreeDifferential (allowed B F) p a)=
      FrozenSignDifferential.differential B F down indep p f := by
    simpa only [a,LinearEquiv.apply_symm_apply] using intertwines B F down indep p a
  have h2 := intertwines B F down indep (p+1) (degreeDifferential (allowed B F) p a)
  rw [h1] at h2
  rw [degreeDifferential_squared (allowed B F) (faces B F down indep),map_zero] at h2
  exact h2.symm

#print axioms face_evaluation
#print axioms intertwines
#print axioms differential_squared
end Verification.FrozenSignIntertwiner
