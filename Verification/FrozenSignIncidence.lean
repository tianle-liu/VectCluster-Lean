/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FrozenSignFaces

/-!
# Frozen Sign Incidence

Equality-transported original face maps and the literal ordered incidence
coefficient, for arbitrary mutable and frozen index sets.
-/
noncomputable section
namespace Verification.FrozenSignIncidence
open Verification.SignComplex Verification.FrozenSignStates Verification.SignFaceAffine
open Verification.FrozenSignFaces Verification.AnticliqueSubcolumns
variable {V C : Type} [Fintype V] [Fintype C] [DecidableEq V] [LinearOrder (V ⊕ C)]
variable (B : (V ⊕ C) → V → ℤ)

def extension (I J : Finset V) (j : V) (hj : j∉I) (hJ : insert j I=J)
    (hB : ∀ i : I, B (Sum.inl j) i.val=0) : ActualSignLabels.labels B J → ZMod 2 → ActualSignLabels.labels B I := by
  subst J
  exact labelExtension B I j hj hB

theorem extension_state (I J : Finset V) (j : V) (hj : j∉I) (hJ : insert j I=J)
    (hB : ∀ i : I, B (Sum.inl j) i.val=0) (ε : ActualSignLabels.labels B J) (b : ZMod 2) :
    state B I (extension B I J j hj hJ hB ε b)=
      faceState (state B J ε) (Sum.inl j) (decide (b=1)) := by
  subst J
  exact state_extension B I j hj hB ε b

def residue (I J : Finset V) (j : V) (hj : j∉I) (hJ : insert j I=J)
    (hB : ∀ i : I, B (Sum.inl j) i.val=0) :
    (ActualSignLabels.labels B I → ℤ) →ₗ[ℤ] (ActualSignLabels.labels B J → ℤ) where
  toFun f ε := f (extension B I J j hj hJ hB ε 0)-f (extension B I J j hj hJ hB ε 1)
  map_add' f g := by funext ε; simp only [Pi.add_apply];ring
  map_smul' r f := by funext ε;simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply];ring

omit [LinearOrder (V ⊕ C)] in
theorem residue_preserves (I J : Finset V) (j : V) (hj : j∉I) (hJ : insert j I=J)
    (hB : ∀ i : I, B (Sum.inl j) i.val=0) (hI : AS B I) (hASJ : AS B J)
    (w : ℤ) (f : ActualSignLabels.labels B I → ℤ)
    (hf : f∈ActualSignatureLattice.lattice B I hI w) :
    residue B I J j hj hJ hB f∈ActualSignatureLattice.lattice B J hASJ w := by
  subst J
  exact ActualSignResidue.actual_residue_preserves B I j hj hB hI hASJ w f hf

def incidence (J : Finset V) (j : V) : ℤ :=
  (-1)^((J.filter (fun i => (Sum.inl i : V ⊕ C)<Sum.inl j)).card)

omit [DecidableEq V] in
theorem state_incidence (J : Finset V) (ε : ActualSignLabels.labels B J) (j : V) :
    incidenceSign (state B J ε) (Sum.inl j)=incidence (C := C) J j := by
  rw [incidenceSign,incidenceRank,state_holes]
  simp only [zeroSet,Finset.filter_map,Finset.card_map,Function.comp_def,Function.Embedding.inl_apply,incidence]

omit [Fintype V] [Fintype C] [DecidableEq V] in
theorem incidence_ordered [LinearOrder V]
    (horder : ∀ i j : V, (Sum.inl i : V ⊕ C)<Sum.inl j ↔ i<j) (J : Finset V) (j : V) :
    incidence (C := C) J j=(-1)^((J.filter (fun i => i<j)).card) := by
  simp only [incidence,horder]

#print axioms extension
#print axioms extension_state
#print axioms residue
#print axioms residue_preserves
#print axioms incidence
#print axioms state_incidence
#print axioms incidence_ordered
end Verification.FrozenSignIncidence
