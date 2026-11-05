/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Module Unit Automorphisms

Automorphisms of the actual trivial line are exactly multiplication
by units. This is the determinant-trivialization action used when the
article forgets orientations.
-/
noncomputable section
namespace Verification.ModuleUnitAutomorphisms
open CategoryTheory
variable (R : Type) [CommRing R]

abbrev line : ModuleCat R := ModuleCat.of R R

def multiplication (u : Rˣ) : line R ≅ line R :=
  (LinearEquiv.smulOfUnit (R := R) (M := R) u).toModuleIso

variable {R}

theorem hom_apply (e : line R ≅ line R) (r : R) : e.hom r=r*e.hom 1 := by
  have h := e.hom.hom.map_smul r (1:R)
  simpa only [smul_eq_mul,mul_one] using h

def unit (e : line R ≅ line R) : Rˣ where
  val := e.hom 1
  inv := e.inv 1
  val_inv := by
    have h := e.hom_inv_id_apply (1:R)
    change e.symm.hom (e.hom 1)=1 at h
    rw [hom_apply e.symm] at h
    exact h
  inv_val := by
    have h := e.inv_hom_id_apply (1:R)
    rw [hom_apply e] at h
    exact h

theorem multiplication_unit (e : line R ≅ line R) : multiplication R (unit e)=e := by
  apply Iso.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change e.hom 1*r=e.hom r
  rw [hom_apply e r,mul_comm]

theorem unit_multiplication (u : Rˣ) : unit (multiplication R u)=u := by
  apply Units.ext
  change u.val*1=u.val
  exact mul_one _

def equiv : (line R ≅ line R) ≃ Rˣ where
  toFun := unit
  invFun := multiplication R
  left_inv := multiplication_unit
  right_inv := unit_multiplication

#print axioms line
#print axioms multiplication
#print axioms hom_apply
#print axioms unit
#print axioms multiplication_unit
#print axioms unit_multiplication
#print axioms equiv
end Verification.ModuleUnitAutomorphisms
