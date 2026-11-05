/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FreezingLattice
import Mathlib.LinearAlgebra.Prod

/-!
# Complementary Character Lattice

Injectivity, saturation, and scaled retractions descend after
removing a free direct factor unused by the character map.
-/
noncomputable section
namespace Verification.ComplementaryCharacterLattice
variable {M P Q F : Type*} [AddCommGroup M] [AddCommGroup P]
  [AddCommGroup Q] [AddCommGroup F]
variable (e : M ≃ₗ[ℤ] F×Q) (f : P →ₗ[ℤ] M) (hz : ∀ p,(e (f p)).1=0)

def remaining : P →ₗ[ℤ] Q := (LinearMap.snd ℤ F Q).comp (e.toLinearMap.comp f)

include hz in
theorem image (p : P) : e (f p)=(0,remaining e f p) := by
  exact Prod.ext (hz p) rfl

include hz in
theorem injective (hf : Function.Injective f) : Function.Injective (remaining e f) := by
  intro p q h
  apply hf
  apply e.injective
  rw [image e f hz p,image e f hz q,h]

include hz in
theorem saturated (hs : FreezingLattice.Saturated (LinearMap.range f)) :
    FreezingLattice.Saturated (LinearMap.range (remaining e f)) := by
  intro a ha q hq
  obtain ⟨p,hp⟩ := hq
  have hx : a • e.symm (0,q) ∈ LinearMap.range f := by
    refine ⟨p,?_⟩
    apply e.injective
    rw [image e f hz p,map_smul,LinearEquiv.apply_symm_apply,hp]
    simp only [Prod.smul_mk,smul_zero]
  obtain ⟨p,hp⟩ := hs a ha (e.symm (0,q)) hx
  refine ⟨p,?_⟩
  change (e (f p)).2=q
  rw [hp,LinearEquiv.apply_symm_apply]

def remainingRetraction (r : M →ₗ[ℤ] P) : Q →ₗ[ℤ] P :=
  r.comp (e.symm.toLinearMap.comp (LinearMap.inr ℤ F Q))

include hz in
theorem scaled_retraction (r : M →ₗ[ℤ] P) (d : ℤ)
    (hr : r.comp f=d • LinearMap.id) :
    (remainingRetraction e r).comp (remaining e f)=d • LinearMap.id := by
  apply LinearMap.ext
  intro p
  change r (e.symm (0,remaining e f p))=d • p
  rw [← image e f hz p,LinearEquiv.symm_apply_apply]
  exact LinearMap.congr_fun hr p

#print axioms remaining
#print axioms image
#print axioms injective
#print axioms saturated
#print axioms remainingRetraction
#print axioms scaled_retraction
end Verification.ComplementaryCharacterLattice
