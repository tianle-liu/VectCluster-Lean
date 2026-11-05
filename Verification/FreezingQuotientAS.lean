/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FreezingLattice

/-!
# Freezing Quotient AS

Independence and saturation after quotienting the distinguished
column. The residual range is proved to be the image of the original
range in the actual quotient lattice.
-/
namespace Verification.FreezingQuotientAS
open Verification.FreezingLattice
variable {R M U : Type*} [CommRing R]
variable [AddCommGroup M] [AddCommGroup U] [Module R M] [Module R U]

theorem firstSpan_le (f : R × U →ₗ[R] M) : firstSpan f ≤ LinearMap.range f := by
  rintro _ ⟨a,rfl⟩
  exact ⟨(a,0),rfl⟩

theorem residual_range (f : R × U →ₗ[R] M) :
    LinearMap.range (residualColumns f) = (LinearMap.range f).map (firstSpan f).mkQ := by
  apply le_antisymm
  · rintro _ ⟨u,rfl⟩
    exact ⟨f (0,u),⟨(0,u),rfl⟩,rfl⟩
  · rintro _ ⟨_,⟨⟨a,u⟩,rfl⟩,rfl⟩
    refine ⟨u,?_⟩
    change (firstSpan f).mkQ (f (0,u)) = (firstSpan f).mkQ (f (a,u))
    apply (Submodule.Quotient.eq _).mpr
    refine ⟨-a,?_⟩
    change f (-a,0) = f (0,u) - f (a,u)
    rw [← map_sub]
    congr 1
    ext <;> simp

theorem residual_injective (f : R × U →ₗ[R] M) (hf : Function.Injective f) :
    Function.Injective (residualColumns f) := by
  intro x y h
  have hm : f (0,x) - f (0,y) ∈ firstSpan f := (Submodule.Quotient.eq _).mp h
  obtain ⟨a,ha⟩ := hm
  change f (a,0) = f (0,x) - f (0,y) at ha
  rw [← map_sub] at ha
  have hh := congrArg Prod.snd (hf ha)
  change 0 = x - y at hh
  exact sub_eq_zero.mp hh.symm

theorem residual_saturated (f : R × U →ₗ[R] M)
    (hf : Saturated (LinearMap.range f)) : Saturated (LinearMap.range (residualColumns f)) := by
  rw [residual_range]
  exact quotient_preserves_saturation (firstSpan f) (LinearMap.range f) (firstSpan_le f) hf

#print axioms firstSpan_le
#print axioms residual_range
#print axioms residual_injective
#print axioms residual_saturated
end Verification.FreezingQuotientAS
