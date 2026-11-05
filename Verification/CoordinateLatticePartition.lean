/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.Data.Finsupp.Basic

/-!
# Coordinate Lattice Partition

Split a character lattice by an actual subset of its named
coordinates. In particular, selected coordinate vectors are retained,
and columns vanishing on that subset lie in the complementary factor.
-/
noncomputable section
namespace Verification.CoordinateLatticePartition
variable (κ : Type) (P : κ→Prop)

def equiv : (κ→₀ℤ) ≃ₗ[ℤ] (({k // P k}→₀ℤ) × ({k // ¬P k}→₀ℤ)) := by
  classical
  exact {
    toFun := fun z=>(z.subtypeDomain P,z.subtypeDomain (fun k=>¬P k))
    invFun := fun z=>z.1.piecewise z.2
    left_inv := by
      intro z
      ext k
      by_cases hk : P k <;> simp [Finsupp.piecewise,hk]
    right_inv := by
      intro z
      exact Prod.ext (Finsupp.subtypeDomain_piecewise _ _) (Finsupp.subtypeDomain_not_piecewise _ _)
    map_add' := by
      intro z w
      exact Prod.ext Finsupp.subtypeDomain_add Finsupp.subtypeDomain_add
    map_smul' := by
      intro r z
      apply Prod.ext <;> ext k <;> rfl }

theorem first_apply (z : κ→₀ℤ) (k : {k // P k}) : (equiv κ P z).1 k = z k.val := rfl
theorem second_apply (z : κ→₀ℤ) (k : {k // ¬P k}) : (equiv κ P z).2 k = z k.val := rfl

theorem column_first_zero (z : κ→₀ℤ) (hz : ∀ k,P k→z k=0) : (equiv κ P z).1=0 := by
  ext k
  exact hz k.val k.property

theorem coordinate (k : {k // P k}) :
    equiv κ P (Finsupp.single k.val 1)=(Finsupp.single k 1,0) := by
  classical
  apply Prod.ext
  · ext j
    rw [first_apply]
    by_cases h : k=j
    · subst j
      simp
    · simp [Finsupp.single_eq_of_ne (fun hh=>h (Subtype.ext hh)),Finsupp.single_eq_of_ne h]
  · ext j
    rw [second_apply]
    apply Finsupp.single_eq_of_ne
    intro hh
    exact j.property (hh ▸ k.property)

theorem inverse_coordinate (k : {k // P k}) :
    (equiv κ P).symm (Finsupp.single k 1,0)=Finsupp.single k.val 1 := by
  apply (equiv κ P).injective
  rw [LinearEquiv.apply_symm_apply,coordinate]

#print axioms equiv
#print axioms first_apply
#print axioms second_apply
#print axioms column_first_zero
#print axioms coordinate
#print axioms inverse_coordinate
end Verification.CoordinateLatticePartition
