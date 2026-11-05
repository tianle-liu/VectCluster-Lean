/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FrozenSignTerms
import Verification.FrozenSignIncidence

/-!
# Frozen Sign Differential

The original alternating sum of label residues, with its actual degree
indexing, preserves the whole degreewise signature lattice.
-/
noncomputable section
namespace Verification.FrozenSignDifferential
open Verification.FrozenSignTerms Verification.FrozenSignIncidence
variable {V C : Type} [Fintype V] [Fintype C] [DecidableEq V] [LinearOrder (V ⊕ C)]
variable (B : (V ⊕ C) → V → ℤ) (F : Finset V → Prop)
variable (down : ∀ I J, J⊆I → F I → F J)
variable (indep : ∀ I, F I → ∀ i∈I, ∀ j∈I, i≠j → B (Sum.inl j) i=0)

def sourceIndex (p : ℕ) (J : Index F (p+1)) (j : J.val) : Index F p :=
  ⟨J.val.erase j.val,down J.val (J.val.erase j.val) (Finset.erase_subset _ _) J.property.1,
    by rw [Finset.card_erase_of_mem j.property,J.property.2];omega⟩

omit [Fintype V] [Fintype C] [LinearOrder (V ⊕ C)] in
include indep in
theorem face_zero (p : ℕ) (J : Index F (p+1)) (j : J.val) :
    ∀ i : J.val.erase j.val, B (Sum.inl j.val) i.val=0 := by
  intro i
  exact indep J.val J.property.1 i.val (Finset.mem_of_mem_erase i.property) j.val j.property
    (Finset.mem_erase.mp i.property).1

def fiber (p : ℕ) (I : Index F p) : (Labels B F p → ℤ) →ₗ[ℤ] (ActualSignLabels.labels B I.val → ℤ) where
  toFun f ε := f ⟨I,ε⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def faceMap (p : ℕ) (J : Index F (p+1)) (j : J.val) :
    (Labels B F p → ℤ) →ₗ[ℤ] (ActualSignLabels.labels B J.val → ℤ) :=
  (residue B (J.val.erase j.val) J.val j.val (Finset.not_mem_erase _ _)
    (Finset.insert_erase j.property) (face_zero B F indep p J j)).comp
      (fiber B F p (sourceIndex F down p J j))

def differential (p : ℕ) : (Labels B F p → ℤ) →ₗ[ℤ] (Labels B F (p+1) → ℤ) :=
  LinearMap.pi fun q => ∑ j : q.1.val, (incidence (C := C) q.1.val j.val) •
    ((LinearMap.proj q.2).comp (faceMap B F down indep p q.1 j))

theorem differential_apply (p : ℕ) (f : Labels B F p → ℤ) (q : Labels B F (p+1)) :
    differential B F down indep p f q=
      ∑ j : q.1.val, (incidence (C := C) q.1.val j.val) • faceMap B F down indep p q.1 j f q.2 := by
  simp [differential]

variable (hAS : ∀ I, F I → AnticliqueSubcolumns.AS B I) (w : ℤ)

omit [LinearOrder (V ⊕ C)] in
theorem face_preserves (p : ℕ) (J : Index F (p+1)) (j : J.val) (f : Labels B F p → ℤ)
    (hf : f∈lattice B F p hAS w) :
    faceMap B F down indep p J j f∈ActualSignatureLattice.lattice B J.val (hAS J.val J.property.1) w := by
  exact residue_preserves B (J.val.erase j.val) J.val j.val (Finset.not_mem_erase _ _)
    (Finset.insert_erase j.property) (face_zero B F indep p J j)
    (hAS _ (sourceIndex F down p J j).property.1) (hAS J.val J.property.1) w
    (fiber B F p (sourceIndex F down p J j) f) (hf (sourceIndex F down p J j))

theorem differential_preserves (p : ℕ) (f : Labels B F p → ℤ) (hf : f∈lattice B F p hAS w) :
    differential B F down indep p f∈lattice B F (p+1) hAS w := by
  intro J
  have he : (fun ε => differential B F down indep p f ⟨J,ε⟩)=
      ∑ j : J.val, incidence (C := C) J.val j.val • faceMap B F down indep p J j f := by
    funext ε
    simp only [differential_apply,Finset.sum_apply,Pi.smul_apply]
  rw [he]
  apply Submodule.sum_mem
  intro j _
  exact Submodule.smul_mem _ _ (face_preserves B F down indep hAS w p J j f hf)

#print axioms sourceIndex
#print axioms face_zero
#print axioms fiber
#print axioms faceMap
#print axioms differential
#print axioms differential_apply
#print axioms face_preserves
#print axioms differential_preserves
end Verification.FrozenSignDifferential
