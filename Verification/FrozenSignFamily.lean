/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FrozenSignStates
import Verification.SignHomology
import Mathlib.Data.Finset.Sum

/-!
# Frozen Sign Family

All original mutable zero sets and all frozen sign coordinates in the
actual sign cochain complex. Its closure and d²=0 are derived from the matrix.
-/
noncomputable section
namespace Verification.FrozenSignFamily
open Verification.SignComplex Verification.FrozenSignStates
variable {V C : Type} [Fintype V] [Fintype C] [LinearOrder (V ⊕ C)]
variable (B : (V ⊕ C) → V → ℤ) (F : Finset V → Prop)

def family (K : Finset (V ⊕ C)) : Prop := ∃ I, F I ∧ K=zeroSet I

omit [Fintype V] [Fintype C] [LinearOrder (V ⊕ C)] in
theorem family_down (down : ∀ I J, J⊆I → F I → F J) :
    ∀ K L : Finset (V ⊕ C), L⊆K → family F K → family F L := by
  intro K L hLK hK
  obtain ⟨I,hI,rfl⟩ := hK
  refine ⟨L.toLeft,down I L.toLeft ?_ hI,?_⟩
  · intro v hv
    exact (inl_mem_zeroSet I v).mp (hLK (Finset.mem_toLeft.mp hv))
  · ext a
    cases a with
    | inl v => simp
    | inr c =>
      have hc : Sum.inr c∉L := fun h => inr_not_mem_zeroSet I c (hLK h)
      simp [hc]

def allowed : State (V ⊕ C) → Prop := exchangeSignAllowed (matrix B) (family F)

theorem faces (down : ∀ I J, J⊆I → F I → F J)
    (indep : ∀ I, F I → ∀ i∈I, ∀ j∈I, i≠j → B (Sum.inl j) i=0) :
    ∀ s, allowed B F s → ∀ i, s i=none → ∀ b, allowed B F (faceState s i b) := by
  apply exchangeSignAllowed_faces (matrix B) (family F) (family_down F down)
  intro K hK i hi j hj hij
  obtain ⟨I,hI,rfl⟩ := hK
  cases i with
  | inr c => exact (inr_not_mem_zeroSet I c hi).elim
  | inl i =>
    cases j with
    | inr c => exact (inr_not_mem_zeroSet I c hj).elim
    | inl j =>
      have h := indep I hI i (by simpa using hi) j (by simpa using hj)
        (fun he => hij (congrArg Sum.inl he))
      simp [matrix,h]

def complex (down : ∀ I J, J⊆I → F I → F J)
    (indep : ∀ I, F I → ∀ i∈I, ∀ j∈I, i≠j → B (Sum.inl j) i=0) :
    CochainComplex (ModuleCat ℤ) ℕ :=
  SignHomology.complex (allowed B F) (faces B F down indep)

theorem state_allowed (I : Finset V) (hI : F I) (ε : ActualSignLabels.labels B I) :
    allowed B F (state B I ε) := by
  refine ⟨⟨I,hI,state_holes B I ε⟩,?_⟩
  intro i hi
  exact state_equations B I ε ⟨i,by simpa only [state_holes] using hi⟩

def labelsToState (q : Σ I : {I : Finset V // F I}, ActualSignLabels.labels B I.val) :
    {s : State (V ⊕ C) // allowed B F s} :=
  ⟨state B q.1.val q.2,state_allowed B F q.1.val q.1.property q.2⟩

theorem labelsToState_injective : Function.Injective (labelsToState B F) := by
  rintro ⟨⟨I,hI⟩,ε⟩ ⟨⟨J,hJ⟩,η⟩ h
  have hs : state B I ε=state B J η := congrArg Subtype.val h
  have hIJ : I=J := zeroSet_injective (by rw [← state_holes B I ε,← state_holes B J η,hs])
  subst J
  have hε : ε=η := by
    apply (coordinates B I).symm.injective
    apply Subtype.ext
    apply Subtype.ext
    exact hs
  subst η
  rfl

theorem labelsToState_surjective : Function.Surjective (labelsToState B F) := by
  intro s
  obtain ⟨I,hI,hIs⟩ := s.property.1
  let t : {s : {s : State (V ⊕ C) // holes s=zeroSet I} //
      ∀ i : zeroSet (C := C) I, exchangeSignValue (matrix B) s.val i.val=1} :=
    ⟨⟨s.val,hIs⟩,fun i => s.property.2 i.val (by simpa only [hIs] using i.property)⟩
  refine ⟨⟨⟨I,hI⟩,coordinates B I t⟩,?_⟩
  apply Subtype.ext
  change ((coordinates B I).symm (coordinates B I t)).val.val=s.val
  rw [Equiv.symm_apply_apply]

def labelsEquiv : (Σ I : {I : Finset V // F I}, ActualSignLabels.labels B I.val) ≃
    {s : State (V ⊕ C) // allowed B F s} :=
  Equiv.ofBijective (labelsToState B F) ⟨labelsToState_injective B F,labelsToState_surjective B F⟩

theorem labelsEquiv_degree (q : Σ I : {I : Finset V // F I}, ActualSignLabels.labels B I.val) :
    (holes (labelsEquiv B F q).val).card=q.1.val.card := by
  change (holes (state B q.1.val q.2)).card=q.1.val.card
  rw [state_holes]
  exact Finset.card_map _

#print axioms family
#print axioms family_down
#print axioms allowed
#print axioms faces
#print axioms complex
#print axioms state_allowed
#print axioms labelsToState
#print axioms labelsToState_injective
#print axioms labelsToState_surjective
#print axioms labelsEquiv
#print axioms labelsEquiv_degree
end Verification.FrozenSignFamily
