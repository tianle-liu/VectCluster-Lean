/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathSplitRecursion
import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.Module.Projective

/-!
# Path Balanced Pivot

Finite-rank cancellation over arbitrary commutative rings. A split free
quotient of the stated complementary rank forces the original column map to
be injective; this is proved, not postulated as part of a pivot hypothesis.
-/

namespace Verification.PathBalancedPivot

variable {R C M Q : Type*} [CommRing R]
variable [AddCommGroup C] [Module R C] [AddCommGroup M] [Module R M]
variable [AddCommGroup Q] [Module R Q] [Module.Finite R M]

omit [Module.Finite R M] in
/-- The quotient section and the original boundary give a surjection. -/
theorem assembled_surjective (d : C →ₗ[R] M) (q : M →ₗ[R] Q) (s : Q →ₗ[R] M)
    (h : LinearMap.range d=LinearMap.ker q) (hs : q.comp s=LinearMap.id) :
    Function.Surjective (d.coprod s) := by
  intro m
  have hm : m-s (q m) ∈ LinearMap.range d := by
    rw [h,LinearMap.mem_ker,map_sub]
    have hh := LinearMap.congr_fun hs (q m)
    simp only [LinearMap.comp_apply,LinearMap.id_apply] at hh
    rw [hh,sub_self]
  obtain ⟨c,hc⟩ := hm
  refine ⟨(c,q m), ?_⟩
  change d c+s (q m)=m
  rw [hc,sub_add_cancel]

/-- Matching finite free ranks, encoded by an actual equivalence, force injection. -/
theorem boundary_injective (d : C →ₗ[R] M) (q : M →ₗ[R] Q) (s : Q →ₗ[R] M)
    (h : LinearMap.range d=LinearMap.ker q) (hs : q.comp s=LinearMap.id)
    (e : (C × Q) ≃ₗ[R] M) : Function.Injective d := by
  letI : Module.Finite R (C × Q) := Module.Finite.equiv e.symm
  let f : (C × Q) →ₗ[R] (C × Q) := e.symm.toLinearMap.comp (d.coprod s)
  have hf : Function.Surjective f := e.symm.surjective.comp (assembled_surjective d q s h hs)
  have hi := OrzechProperty.injective_of_surjective_endomorphism f hf
  intro x y hxy
  have hh : f (x,0)=f (y,0) := by
    change e.symm (d x+s 0)=e.symm (d y+s 0)
    rw [hxy]
  exact congrArg Prod.fst (hi hh)

/-- The quotient section exists whenever the actual quotient target is projective. -/
theorem exists_coordinates [Module.Projective R Q]
    (d : C →ₗ[R] M) (q : M →ₗ[R] Q) (hq : Function.Surjective q)
    (h : LinearMap.range d=LinearMap.ker q) (e : (C × Q) ≃ₗ[R] M) :
    ∃ E : M ≃ₗ[R] (C × Q), ∀ c, E (d c)=(c,0) := by
  obtain ⟨s,hs⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  have hd := boundary_injective d q s h hs e
  refine ⟨Verification.PathSplitRecursion.coordinates d q s hd h hs, ?_⟩
  intro c
  apply Prod.ext
  · exact Verification.PathSplitRecursion.closedRetraction_closed d q s hd h hs c
  · exact Verification.PathSplitRecursion.open_closed d q h c

/-- This applies to the literal cokernel, rather than an independently posited row. -/
theorem exists_coordinates_of_cokernel [Module.Projective R Q]
    (d : C →ₗ[R] M) (coker : (M ⧸ LinearMap.range d) ≃ₗ[R] Q)
    (e : (C × Q) ≃ₗ[R] M) :
    ∃ E : M ≃ₗ[R] (C × Q), ∀ c, E (d c)=(c,0) := by
  let q : M →ₗ[R] Q := coker.toLinearMap.comp (LinearMap.range d).mkQ
  apply exists_coordinates d q
  · exact coker.surjective.comp (LinearMap.range_eq_top.mp (LinearMap.range d).range_mkQ)
  · change _=LinearMap.ker (coker.toLinearMap.comp (LinearMap.range d).mkQ)
    rw [LinearMap.ker_comp,LinearEquiv.ker,Submodule.comap_bot,Submodule.ker_mkQ]
  · exact e

#print axioms assembled_surjective
#print axioms boundary_injective
#print axioms exists_coordinates
#print axioms exists_coordinates_of_cokernel

end Verification.PathBalancedPivot
