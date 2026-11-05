/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SignFaceAffine
import Verification.SignatureResidue

/-!
# Actual Sign Residue

The literal positive-minus-negative map on the article's actual affine
sign labels preserves Λ_s→Λ_(s-1), including all actual coordinate choices.
-/
noncomputable section
namespace Verification.ActualSignResidue
open Verification.SignFaceAffine Verification.ActualSignatureLattice
open Verification.AffineSignCoordinates Verification.SignatureLabelLattice
open Verification.BooleanAffineLattice Verification.BooleanCubeCoordinates
open Verification.SignatureLattice Verification.AffineSignature
variable {α : Type*} [DecidableEq α]

def normalVector (S : Finset α) (b : ZMod 2) : Option α → ZMod 2 :=
  fun a => match a with | none => b | some a => vector S a

theorem vector_positive (S : Finset α) : vector (S.image some)=normalVector S 0 := by
  funext a
  cases a <;> simp [vector,normalVector]

theorem vector_negative (S : Finset α) : vector (insert none (S.image some))=normalVector S 1 := by
  funext a
  cases a <;> simp [vector,normalVector]

variable {V C : Type*} [Fintype V] [Fintype C] [DecidableEq V]

def residue (B : (V ⊕ C) → V → ℤ) (I : Finset V) (j : V) (hj : j∉I)
    (hB : ∀ i : I, B (Sum.inl j) i.val=0) :
    (ActualSignLabels.labels B I → ℤ) →ₗ[ℤ] (ActualSignLabels.labels B (insert j I) → ℤ) where
  toFun f ε := f (labelExtension B I j hj hB ε 0)-f (labelExtension B I j hj hB ε 1)
  map_add' f g := by funext ε; simp only [Pi.add_apply]; ring
  map_smul' r f := by funext ε; simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply];ring

theorem cube_face (B : (V ⊕ C) → V → ℤ) (I : Finset V) (j : V) (hj : j∉I)
    (hB : ∀ i : I, B (Sum.inl j) i.val=0)
    (p : ActualSignLabels.labels B I) (q : ActualSignLabels.labels B (insert j I))
    (T : Finset (Option (Index (reduced B (insert j I))))) :
    (labelCube (reduced B I) (fun _ => 1) p).symm (asFinset (face B I j hj p q) T)=
      labelExtension B I j hj hB
        ((coordinates (reduced B (insert j I)) (fun _ => 1) q).symm (tail _ (vector T)))
        (vector T none) := by
  change (coordinates (reduced B I) (fun _ => 1) p).symm (vector (asFinset (face B I j hj p q) T))=_
  rw [vector_asFinset]
  exact face_extension B I j hj hB p q _

theorem cube_face_positive (B : (V ⊕ C) → V → ℤ) (I : Finset V) (j : V) (hj : j∉I)
    (hB : ∀ i : I, B (Sum.inl j) i.val=0)
    (p : ActualSignLabels.labels B I) (q : ActualSignLabels.labels B (insert j I))
    (S : Finset (Index (reduced B (insert j I)))) :
    (labelCube (reduced B I) (fun _ => 1) p).symm (asFinset (face B I j hj p q) (S.image some))=
      labelExtension B I j hj hB ((labelCube (reduced B (insert j I)) (fun _ => 1) q).symm S) 0 := by
  rw [cube_face B I j hj hB,vector_positive]
  rfl

theorem cube_face_negative (B : (V ⊕ C) → V → ℤ) (I : Finset V) (j : V) (hj : j∉I)
    (hB : ∀ i : I, B (Sum.inl j) i.val=0)
    (p : ActualSignLabels.labels B I) (q : ActualSignLabels.labels B (insert j I))
    (S : Finset (Index (reduced B (insert j I)))) :
    (labelCube (reduced B I) (fun _ => 1) p).symm
        (asFinset (face B I j hj p q) (insert none (S.image some)))=
      labelExtension B I j hj hB ((labelCube (reduced B (insert j I)) (fun _ => 1) q).symm S) 1 := by
  rw [cube_face B I j hj hB,vector_negative]
  rfl

theorem toCube_residue (B : (V ⊕ C) → V → ℤ) (I : Finset V) (j : V) (hj : j∉I)
    (hB : ∀ i : I, B (Sum.inl j) i.val=0)
    (p : ActualSignLabels.labels B I) (q : ActualSignLabels.labels B (insert j I))
    (f : ActualSignLabels.labels B I → ℤ) :
    toCube (reduced B (insert j I)) (fun _ => 1) q (residue B I j hj hB f)=
      SignatureResidue.residue (pullback (asFinset (face B I j hj p q))
        (toCube (reduced B I) (fun _ => 1) p f)) := by
  funext S
  change f (labelExtension B I j hj hB ((labelCube (reduced B (insert j I)) (fun _ => 1) q).symm S) 0)-
      f (labelExtension B I j hj hB ((labelCube (reduced B (insert j I)) (fun _ => 1) q).symm S) 1)=
    f ((labelCube (reduced B I) (fun _ => 1) p).symm (asFinset (face B I j hj p q) (S.image some)))-
      f ((labelCube (reduced B I) (fun _ => 1) p).symm (asFinset (face B I j hj p q) (insert none (S.image some))))
  rw [cube_face_positive B I j hj hB,cube_face_negative B I j hj hB]

theorem residue_preserves (B : (V ⊕ C) → V → ℤ) (I : Finset V) (j : V) (hj : j∉I)
    (hB : ∀ i : I, B (Sum.inl j) i.val=0)
    (p : ActualSignLabels.labels B I) (q : ActualSignLabels.labels B (insert j I))
    (s : ℤ) (f : ActualSignLabels.labels B I → ℤ)
    (hf : f∈SignatureLabelLattice.lattice (reduced B I) (fun _ => 1) p s) :
    residue B I j hj hB f∈SignatureLabelLattice.lattice (reduced B (insert j I)) (fun _ => 1) q (s-1) := by
  have h := SignatureResidue.residue_preserves_lattice s _
    (affine_preserves (face B I j hj p q) s (toCube (reduced B I) (fun _ => 1) p f) hf)
  rw [← toCube_residue B I j hj hB p q f] at h
  exact h

theorem actual_residue_preserves (B : (V ⊕ C) → V → ℤ) (I : Finset V) (j : V) (hj : j∉I)
    (hB : ∀ i : I, B (Sum.inl j) i.val=0)
    (hI : AnticliqueSubcolumns.AS B I) (hJ : AnticliqueSubcolumns.AS B (insert j I))
    (w : ℤ) (f : ActualSignLabels.labels B I → ℤ) (hf : f∈ActualSignatureLattice.lattice B I hI w) :
    residue B I j hj hB f∈ActualSignatureLattice.lattice B (insert j I) hJ w := by
  have h := residue_preserves B I j hj hB (basepoint B I hI) (basepoint B (insert j I) hJ)
    (w-I.card) f hf
  have he : w-((insert j I).card:ℤ)=(w-I.card)-1 := by rw [Finset.card_insert_of_not_mem hj];omega
  change residue B I j hj hB f∈SignatureLabelLattice.lattice _ _ _ _
  rw [he]
  exact h

#print axioms normalVector
#print axioms vector_positive
#print axioms vector_negative
#print axioms residue
#print axioms cube_face
#print axioms cube_face_positive
#print axioms cube_face_negative
#print axioms toCube_residue
#print axioms residue_preserves
#print axioms actual_residue_preserves
end Verification.ActualSignResidue
