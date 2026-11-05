/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SignatureLabelLattice

/-!
# Actual Signature Lattice

The actual stratum lattice Λ_(j-|I|)(E_I), with the article's precise
degree-dependent power of two, derived from AS and actual affine coordinates.
-/
noncomputable section
namespace Verification.ActualSignatureLattice
open Verification.AnticliqueSubcolumns
variable {V C : Type*} [Fintype V] [Fintype C]

def reduced (B : (V ⊕ C) → V → ℤ) (I : Finset V) : Rows (C := C) I → I → ℤ :=
  fun a i => B a.val i.val

def basepoint (B : (V ⊕ C) → V → ℤ) (I : Finset V) (hAS : AS B I) :
    AffineSignCoordinates.labels (reduced B I) (fun _ => 1) :=
  (ActualSignLabels.nonempty_labels B I hAS).some

def lattice (B : (V ⊕ C) → V → ℤ) (I : Finset V) (hAS : AS B I) (j : ℤ) :
    Submodule ℤ (ActualSignLabels.labels B I → ℤ) :=
  SignatureLabelLattice.lattice (reduced B I) (fun _ => 1) (basepoint B I hAS) (j-I.card)

theorem any_origin (B : (V ⊕ C) → V → ℤ) (I : Finset V) (hAS : AS B I)
    (p : ActualSignLabels.labels B I) (j : ℤ) : lattice B I hAS j=
      SignatureLabelLattice.lattice (reduced B I) (fun _ => 1) p (j-I.card) :=
  SignatureLabelLattice.lattice_origin_independent _ _ _ _ _

theorem bound_exponent (B : (V ⊕ C) → V → ℤ) (I : Finset V) (hAS : AS B I) (j : ℤ) :
    ((Module.finrank (ZMod 2) (LinearMap.ker (AffineSignCoordinates.linear (reduced B I)))):ℤ)-
      (j-I.card)=(Fintype.card V+Fintype.card C:ℤ)-I.card-j := by
  have hd : Module.finrank (ZMod 2) (LinearMap.ker (AffineSignCoordinates.linear (reduced B I)))=
      Fintype.card V+Fintype.card C-2*I.card := AffineSignCoordinates.actual_dimension B I hAS
  rw [hd]
  have h := ActualSignLabels.twice_card_le_dimension B I hAS
  omega

theorem scaled_function_mem (B : (V ⊕ C) → V → ℤ) (I : Finset V) (hAS : AS B I)
    (j : ℤ) (f : ActualSignLabels.labels B I → ℤ) :
    (2:ℤ)^((Fintype.card V+Fintype.card C:ℤ)-I.card-j).toNat • f ∈ lattice B I hAS j := by
  have h := SignatureLabelLattice.scaled_function_mem (reduced B I) (fun _ => 1)
    (basepoint B I hAS) (j-I.card) f
  rwa [bound_exponent B I hAS] at h

theorem lattice_eq_top (B : (V ⊕ C) → V → ℤ) (I : Finset V) (hAS : AS B I)
    (j : ℤ) (hj : (Fintype.card V+Fintype.card C:ℤ)-I.card≤j) : lattice B I hAS j=⊤ := by
  apply top_unique
  intro f _
  have h := scaled_function_mem B I hAS j f
  have he : ((Fintype.card V+Fintype.card C:ℤ)-I.card-j).toNat=0 := by omega
  simpa only [he,pow_zero,one_smul] using h

#print axioms reduced
#print axioms basepoint
#print axioms lattice
#print axioms any_origin
#print axioms bound_exponent
#print axioms scaled_function_mem
#print axioms lattice_eq_top
end Verification.ActualSignatureLattice
