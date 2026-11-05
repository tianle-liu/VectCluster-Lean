/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Logic.Equiv.Defs

/-!
# Unit Normalized Classification

A classifier differing from a bijection by a fixed invertible
scalar is again a bijection. This handles the cited comparison of the
obstruction Euler class with the Chow--Witt Euler class.
-/
noncomputable section
namespace Verification.UnitNormalizedClassification
variable {X H G : Type*} [Group G] [MulAction G H]
variable (E : X ≃ H) (f : X → H) (u : G) (hc : ∀ x,E x=u • f x)

def equivalence : X ≃ H where
  toFun := f
  invFun y := E.symm (u • y)
  left_inv x := by
    change E.symm (u • f x)=x
    rw [←hc x,E.symm_apply_apply]
  right_inv y := by
    have he := hc (E.symm (u • y))
    rw [E.apply_symm_apply] at he
    have h := congrArg (fun z => u⁻¹ • z) he
    simpa only [inv_smul_smul] using h.symm

theorem equivalence_apply (x : X) : equivalence E f u hc x=f x := rfl

#print axioms equivalence
#print axioms equivalence_apply
end Verification.UnitNormalizedClassification
