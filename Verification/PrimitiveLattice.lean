/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FreezingLattice
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.EuclideanDomain.Int

/-!
# Primitive Lattice

The AS lattice-to-coordinate step used by the original geometry and
freezing arguments. Saturation implies a torsion-free quotient; over ℤ the
finite quotient is free. We then construct the actual lattice splitting,
instead of assuming that primitive columns already come with coordinates.
-/
namespace Verification.PrimitiveLattice
variable {M P : Type*} [AddCommGroup M] [AddCommGroup P]

/-- An actual saturated lattice quotient has no integer torsion. -/
theorem quotient_torsionFree (S : Submodule ℤ M)
    (hS : Verification.FreezingLattice.Saturated S) : NoZeroSMulDivisors ℤ (M ⧸ S) := by
  constructor
  intro a x hax
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    refine Submodule.Quotient.induction_on S x ?_ hax
    intro m hm
    apply (Submodule.Quotient.mk_eq_zero S).mpr
    apply hS a ha m
    apply (Submodule.Quotient.mk_eq_zero S).mp
    exact hm

theorem quotient_free [Module.Finite ℤ M] (S : Submodule ℤ M)
    (hS : Verification.FreezingLattice.Saturated S) : Module.Free ℤ (M ⧸ S) := by
  letI := quotient_torsionFree S hS
  exact Module.free_of_finite_type_torsion_free'

theorem quotient_section [Module.Finite ℤ M] (S : Submodule ℤ M)
    (hS : Verification.FreezingLattice.Saturated S) :
    ∃ t : (M ⧸ S) →ₗ[ℤ] M, S.mkQ.comp t = LinearMap.id := by
  letI := quotient_free S hS
  exact S.mkQ.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr S.mkQ_surjective)

def projection (S : Submodule ℤ M) (t : (M ⧸ S) →ₗ[ℤ] M)
    (ht : S.mkQ.comp t = LinearMap.id) : M →ₗ[ℤ] S :=
  (LinearMap.id - t.comp S.mkQ).codRestrict S (by
    intro m
    apply (Submodule.Quotient.mk_eq_zero S).mp
    change S.mkQ (m - t (S.mkQ m)) = 0
    have htq := LinearMap.congr_fun ht (S.mkQ m)
    change S.mkQ (t (S.mkQ m)) = S.mkQ m at htq
    rw [map_sub, htq, sub_self])

/-- The actual lattice coordinate decomposition, with both inverse maps. -/
def splitting (S : Submodule ℤ M) (t : (M ⧸ S) →ₗ[ℤ] M)
    (ht : S.mkQ.comp t = LinearMap.id) : M ≃ₗ[ℤ] (S × (M ⧸ S)) where
  toFun m := (projection S t ht m, S.mkQ m)
  invFun z := z.1.val + t z.2
  left_inv m := by simp [projection]
  right_inv z := by
    have hu : S.mkQ z.1.val = 0 := (Submodule.Quotient.mk_eq_zero S).mpr z.1.property
    have htq := LinearMap.congr_fun ht z.2
    change S.mkQ (t z.2) = z.2 at htq
    apply Prod.ext
    · apply Subtype.ext
      change z.1.val + t z.2 - t (S.mkQ (z.1.val + t z.2)) = z.1.val
      rw [map_add, hu, zero_add, htq, add_sub_cancel_right]
    · change S.mkQ (z.1.val + t z.2) = z.2
      rw [map_add, hu, htq, zero_add]
  map_add' a b := by simp
  map_smul' a b := by simp

/-- Primitive independent columns admit a complement, with no extra
splitting assumption. This is the AS input needed by the torus calculation. -/
theorem primitive_columns_split [Module.Finite ℤ M]
    (f : P →ₗ[ℤ] M) (hf : Function.Injective f)
    (hs : Verification.FreezingLattice.Saturated (LinearMap.range f)) :
    Nonempty (M ≃ₗ[ℤ] (P × (M ⧸ LinearMap.range f))) := by
  obtain ⟨t, ht⟩ := quotient_section (LinearMap.range f) hs
  exact ⟨(splitting (LinearMap.range f) t ht).trans
    (((LinearEquiv.ofInjective f hf).symm).prodCongr (LinearEquiv.refl ℤ _))⟩

noncomputable def columnSplitting (f : P →ₗ[ℤ] M) (hf : Function.Injective f)
    (t : (M ⧸ LinearMap.range f) →ₗ[ℤ] M)
    (ht : (LinearMap.range f).mkQ.comp t = LinearMap.id) :
    M ≃ₗ[ℤ] (P × (M ⧸ LinearMap.range f)) :=
  (splitting (LinearMap.range f) t ht).trans
    (((LinearEquiv.ofInjective f hf).symm).prodCongr (LinearEquiv.refl ℤ _))

theorem columnSplitting_apply (f : P →ₗ[ℤ] M) (hf : Function.Injective f)
    (t : (M ⧸ LinearMap.range f) →ₗ[ℤ] M)
    (ht : (LinearMap.range f).mkQ.comp t = LinearMap.id) (p : P) :
    columnSplitting f hf t ht (f p) = (p,0) := by
  have hz : (LinearMap.range f).mkQ (f p) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨p,rfl⟩
  apply Prod.ext
  · change (LinearEquiv.ofInjective f hf).symm (projection _ t ht (f p)) = p
    apply (LinearEquiv.ofInjective f hf).injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    change f p - t ((LinearMap.range f).mkQ (f p)) = f p
    rw [hz, map_zero, sub_zero]
  · exact hz

theorem primitive_columns_split_compatible [Module.Finite ℤ M]
    (f : P →ₗ[ℤ] M) (hf : Function.Injective f)
    (hs : Verification.FreezingLattice.Saturated (LinearMap.range f)) :
    ∃ e : M ≃ₗ[ℤ] (P × (M ⧸ LinearMap.range f)), ∀ p, e (f p) = (p,0) := by
  obtain ⟨t,ht⟩ := quotient_section (LinearMap.range f) hs
  exact ⟨columnSplitting f hf t ht, columnSplitting_apply f hf t ht⟩

#print axioms columnSplitting
#print axioms columnSplitting_apply
#print axioms primitive_columns_split_compatible
#print axioms quotient_torsionFree
#print axioms quotient_free
#print axioms quotient_section
#print axioms projection
#print axioms splitting
#print axioms primitive_columns_split
end Verification.PrimitiveLattice
