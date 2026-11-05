/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.BooleanCubeCoordinates
import Verification.AffineSignCoordinates

/-!
# Signature Label Lattice

The actual lattice on a sign-label affine space. Its independence of
the chosen origin is proved by the affine coordinate transition, and its
uniform denominator bound is a statement about actual label functions.
-/
noncomputable section
namespace Verification.SignatureLabelLattice
open Verification.AffineSignCoordinates Verification.BooleanAffineLattice
open Verification.BooleanCubeCoordinates Verification.SignatureLattice Verification.AffineSignature
variable {ι κ : Type*} [Fintype κ]

abbrev Index (B : κ → ι → ℤ) := Fin (Module.finrank (ZMod 2) (LinearMap.ker (linear B)))

def labelCube (B : κ → ι → ℤ) (u : ι → ZMod 2) (p : labels B u) :
    labels B u ≃ Finset (Index B) := (coordinates B u p).trans cubeEquiv.symm

def toCube (B : κ → ι → ℤ) (u : ι → ZMod 2) (p : labels B u) :
    (labels B u → ℤ) →ₗ[ℤ] (Finset (Index B) → ℤ) where
  toFun f S := f ((labelCube B u p).symm S)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def transition (B : κ → ι → ℤ) (u : ι → ZMod 2) (p q : labels B u) :
    (Index B → ZMod 2) →ᵃ[ZMod 2] (Index B → ZMod 2) :=
  (decode B u q).comp (encode B u p)

theorem coordinates_transition (B : κ → ι → ℤ) (u : ι → ZMod 2) (p q : labels B u)
    (x : Index B → ZMod 2) :
    (coordinates B u q).symm (transition B u p q x)=(coordinates B u p).symm x := by
  apply (coordinates B u q).injective
  rw [Equiv.apply_symm_apply,coordinates_apply,coordinates_symm_apply]
  rfl

theorem cube_transition (B : κ → ι → ℤ) (u : ι → ZMod 2) (p q : labels B u)
    (S : Finset (Index B)) :
    (labelCube B u q).symm (asFinset (transition B u p q) S)=(labelCube B u p).symm S := by
  change (coordinates B u q).symm (vector (asFinset (transition B u p q) S))=
    (coordinates B u p).symm (vector S)
  rw [vector_asFinset]
  exact coordinates_transition B u p q _

theorem toCube_transition (B : κ → ι → ℤ) (u : ι → ZMod 2) (p q : labels B u)
    (f : labels B u → ℤ) :
    pullback (asFinset (transition B u p q)) (toCube B u q f)=toCube B u p f := by
  funext S
  change f ((labelCube B u q).symm (asFinset (transition B u p q) S))=f ((labelCube B u p).symm S)
  rw [cube_transition]

def lattice (B : κ → ι → ℤ) (u : ι → ZMod 2) (p : labels B u) (s : ℤ) :
    Submodule ℤ (labels B u → ℤ) := (signatureLattice s).comap (toCube B u p)

theorem lattice_origin_independent (B : κ → ι → ℤ) (u : ι → ZMod 2)
    (p q : labels B u) (s : ℤ) : lattice B u p s=lattice B u q s := by
  ext f
  change toCube B u p f∈signatureLattice s ↔ toCube B u q f∈signatureLattice s
  constructor
  · intro hf
    have h := affine_preserves (transition B u q p) s (toCube B u p f) hf
    rwa [toCube_transition] at h
  · intro hf
    have h := affine_preserves (transition B u p q) s (toCube B u q f) hf
    rwa [toCube_transition] at h

theorem scaled_function_mem (B : κ → ι → ℤ) (u : ι → ZMod 2)
    (p : labels B u) (s : ℤ) (f : labels B u → ℤ) :
    (2:ℤ)^((Module.finrank (ZMod 2) (LinearMap.ker (linear B)):ℤ)-s).toNat • f ∈ lattice B u p s := by
  change toCube B u p (_ • f)∈signatureLattice s
  rw [map_smul]
  simpa only [boundExponent,Fintype.card_fin] using
    SignatureLattice.scaled_function_mem s (toCube B u p f)

theorem lattice_eq_top (B : κ → ι → ℤ) (u : ι → ZMod 2)
    (p : labels B u) (s : ℤ) (hs : (Module.finrank (ZMod 2) (LinearMap.ker (linear B)):ℤ)≤s) :
    lattice B u p s=⊤ := by
  unfold lattice
  rw [signatureLattice_eq_top s (by simpa using hs),Submodule.comap_top]

#print axioms Index
#print axioms labelCube
#print axioms toCube
#print axioms transition
#print axioms coordinates_transition
#print axioms cube_transition
#print axioms toCube_transition
#print axioms lattice
#print axioms lattice_origin_independent
#print axioms scaled_function_mem
#print axioms lattice_eq_top
end Verification.SignatureLabelLattice
