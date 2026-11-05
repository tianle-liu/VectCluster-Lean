/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GradedPerturbation
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Degree Basis Coordinates

Explicit finite bases for a specified degree, indexed by any proved
bijection with its actual subset of coordinate indices.
-/

namespace Verification.DegreeBasisCoordinates

open Verification.GradedPerturbation

variable {R : Type*} [CommRing R]
variable {ι α : Type*} [Fintype α]
open Classical

noncomputable def coordinateEquiv (d : ι → ℤ) (p : ℤ) (e : α ≃ {i // d i=p}) :
    degreeModule (R := R) d p ≃ₗ[R] (α → R) := by
  classical
  exact {
    toFun := fun x a => x.val (e a).val
    invFun := fun y => ⟨fun i => if hi : d i=p then y (e.symm ⟨i,hi⟩) else 0,
      by intro i hi; simp [hi]⟩
    left_inv := by
      intro x
      apply Subtype.ext
      funext i
      by_cases hi : d i=p
      · simp only [hi,↓reduceDIte,e.apply_symm_apply]
      · simp only [hi,↓reduceDIte,x.property i hi]
    right_inv := by
      intro y
      funext a
      simp only [(e a).property,↓reduceDIte,e.symm_apply_apply]
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

noncomputable def basisEquiv (d : ι → ℤ) (p : ℤ) (e : α ≃ {i // d i=p}) :
    degreeModule (R := R) d p ≃ₗ[R] (α →₀ R) :=
  (coordinateEquiv d p e).trans (Finsupp.linearEquivFunOnFinite R R α).symm

theorem basis_apply (d : ι → ℤ) (p : ℤ) (e : α ≃ {i // d i=p})
    (x : degreeModule (R := R) d p) (a : α) : basisEquiv d p e x a=x.val (e a).val := rfl

theorem basis_inverse_single (d : ι → ℤ) (p : ℤ) (e : α ≃ {i // d i=p}) (a : α) (r : R) :
    ((basisEquiv d p e).symm (Finsupp.single a r)).val=Pi.single (e a).val r := by
  classical
  funext i
  change (if hi : d i=p then (Finsupp.single a r) (e.symm ⟨i,hi⟩) else 0)=(Pi.single (e a).val r : ι → R) i
  by_cases hi : d i=p
  · rw [dif_pos hi]
    by_cases he : i=(e a).val
    · subst i
      change (Finsupp.single a r) (e.symm (e a))=(Pi.single (e a).val r : ι → R) (e a).val
      simp only [Equiv.symm_apply_apply,Finsupp.single_eq_same,Pi.single_eq_same]
    · have hn : a ≠ e.symm ⟨i,hi⟩ := by
        intro hh
        have heq := congrArg (fun a => (e a).val) hh
        simp only [Equiv.apply_symm_apply] at heq
        exact he heq.symm
      rw [Finsupp.single_eq_of_ne hn,Pi.single_eq_of_ne he]
  · rw [dif_neg hi]
    have he : i ≠ (e a).val := by intro hh; apply hi; rw [hh]; exact (e a).property
    rw [Pi.single_eq_of_ne he]

#print axioms coordinateEquiv
#print axioms basisEquiv
#print axioms basis_apply
#print axioms basis_inverse_single

end Verification.DegreeBasisCoordinates
