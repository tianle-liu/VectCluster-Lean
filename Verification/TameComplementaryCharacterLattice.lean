/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ComplementaryCharacterLattice
import Verification.SmithScaledRetraction

/-!
# Tame Complementary Character Lattice

Tameness passes to the complementary character lattice after a
free direct factor is removed. This is proved over the integers, using
a scaled left inverse; no characteristic-zero assumption is added.
-/
noncomputable section
namespace Verification.TameComplementaryCharacterLattice
open Verification.ComplementaryCharacterLattice Verification.SmithScaledRetraction
variable {M P Q F ι κ : Type*} [AddCommGroup M] [AddCommGroup P]
  [AddCommGroup Q] [AddCommGroup F]
variable (f : P →ₗ[ℤ] M) (hf : Function.Injective f)
variable {n : ℕ} (s : Basis.SmithNormalForm (LinearMap.range f) ι n)

def sourceRetraction : M →ₗ[ℤ] P :=
  (LinearEquiv.ofInjective f hf).symm.toLinearMap.comp (retraction s)

theorem sourceRetraction_comp :
    (sourceRetraction f hf s).comp f=denominator s • LinearMap.id := by
  apply LinearMap.ext
  intro p
  have h := LinearMap.congr_fun (retraction_subtype s) ((LinearEquiv.ofInjective f hf) p)
  change retraction s (f p)=denominator s • (LinearEquiv.ofInjective f hf) p at h
  change (LinearEquiv.ofInjective f hf).symm (retraction s (f p))=denominator s • p
  rw [h,map_smul,LinearEquiv.symm_apply_apply]

def rangeRetraction (g : P →ₗ[ℤ] Q) (r : Q →ₗ[ℤ] P) : Q →ₗ[ℤ] LinearMap.range g :=
  g.rangeRestrict.comp r

theorem rangeRetraction_comp (g : P →ₗ[ℤ] Q) (r : Q →ₗ[ℤ] P) (d : ℤ)
    (hr : r.comp g=d • LinearMap.id) :
    (rangeRetraction g r).comp (LinearMap.range g).subtype=d • LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨q,p,hp⟩
  apply Subtype.ext
  change g (r q)=d • q
  rw [← hp]
  have h := LinearMap.congr_fun hr p
  change r (g p)=d • p at h
  rw [h,map_smul]

variable (e : M ≃ₗ[ℤ] F×Q) (hz : ∀ p,(e (f p)).1=0)
variable (R : Type*) [CommRing R]

include hf hz in
theorem remaining_tame {m : ℕ}
    (t : Basis.SmithNormalForm (LinearMap.range (remaining e f)) κ m)
    (he : ∀ i,IsUnit ((s.a i).natAbs:R)) : ∀ i,IsUnit ((t.a i).natAbs:R) := by
  let r := remainingRetraction e (sourceRetraction f hf s)
  have hr : r.comp (remaining e f)=denominator s • LinearMap.id :=
    scaled_retraction e f hz _ _ (sourceRetraction_comp f hf s)
  exact coefficients_unit_of_retraction t R
    (rangeRetraction (remaining e f) r) (denominator s)
    (rangeRetraction_comp (remaining e f) r (denominator s) hr)
    (denominator_unit s R he)

#print axioms sourceRetraction
#print axioms sourceRetraction_comp
#print axioms rangeRetraction
#print axioms rangeRetraction_comp
#print axioms remaining_tame
end Verification.TameComplementaryCharacterLattice
