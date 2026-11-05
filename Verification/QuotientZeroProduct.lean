/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FreezingLattice

/-!
# Quotient Zero Product

Quotient a lattice with a displayed free summand by a column lying
entirely in the other summand. The equivalence is constructed by the first
isomorphism theorem, with the kernel and surjectivity proved explicitly.
-/
noncomputable section
namespace Verification.QuotientZeroProduct
open Verification.FreezingLattice
variable {R L U M P : Type*} [CommRing R]
variable [AddCommGroup L] [AddCommGroup U] [AddCommGroup M] [AddCommGroup P]
variable [Module R L] [Module R U] [Module R M] [Module R P]
variable (e : L ≃ₗ[R] U × M) (f : R × P →ₗ[R] L) (b : R →ₗ[R] M)

def project : L →ₗ[R] U × (M ⧸ LinearMap.range b) :=
  ((LinearMap.id : U →ₗ[R] U).prodMap (LinearMap.range b).mkQ).comp e.toLinearMap

theorem project_surjective : Function.Surjective (project e b) := by
  rintro ⟨u,q⟩
  obtain ⟨m,rfl⟩ := (LinearMap.range b).mkQ_surjective q
  refine ⟨e.symm (u,m),?_⟩
  change ((e (e.symm (u,m))).1, (LinearMap.range b).mkQ (e (e.symm (u,m))).2) = _
  rw [LinearEquiv.apply_symm_apply]

theorem project_kernel (hhead : ∀ a, e (f (a,0)) = (0,b a)) :
    LinearMap.ker (project e b) = firstSpan f := by
  ext x
  constructor
  · intro hx
    have hz : (e x).1 = 0 ∧ (LinearMap.range b).mkQ (e x).2 = 0 := Prod.mk.inj hx
    obtain ⟨a,ha⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz.2
    refine ⟨a,?_⟩
    apply e.injective
    change e (f (a,0)) = e x
    rw [hhead]
    exact Prod.ext hz.1.symm ha
  · rintro ⟨a,rfl⟩
    change ((e (f (a,0))).1, (LinearMap.range b).mkQ (e (f (a,0))).2) = 0
    rw [hhead]
    apply Prod.ext
    · rfl
    · exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨a,rfl⟩

def quotientEquiv (hhead : ∀ a, e (f (a,0)) = (0,b a)) :
    (L ⧸ firstSpan f) ≃ₗ[R] U × (M ⧸ LinearMap.range b) :=
  (Submodule.quotEquivOfEq _ _ (project_kernel e f b hhead).symm).trans
    (LinearMap.quotKerEquivOfSurjective (project e b) (project_surjective e b))

theorem quotientEquiv_mk (hhead : ∀ a, e (f (a,0)) = (0,b a)) (x : L) :
    quotientEquiv e f b hhead ((firstSpan f).mkQ x) =
      ((e x).1, (LinearMap.range b).mkQ (e x).2) := rfl

#print axioms project
#print axioms project_surjective
#print axioms project_kernel
#print axioms quotientEquiv
#print axioms quotientEquiv_mk
end Verification.QuotientZeroProduct
