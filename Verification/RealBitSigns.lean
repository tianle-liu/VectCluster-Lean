/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RealOrthants
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

/-!
# Real Bit Signs

The exact relation between F₂ sign equations and real monomial signs.
-/
noncomputable section
namespace Verification.RealBitSigns

def unit (x : ZMod 2) : ℝˣ := Units.mk0 (if x=0 then 1 else -1) (by split_ifs <;> norm_num)

theorem unit_zero : unit 0=1 := by ext; simp [unit]

theorem unit_one : (unit 1 : ℝ) = -1 := by simp [unit]

theorem unit_add (x y : ZMod 2) : unit (x+y)=unit x*unit y := by
  fin_cases x <;> fin_cases y <;> apply Units.ext <;>
    norm_num [unit,show (1:ZMod 2)+1=0 from rfl]

def character : Multiplicative (ZMod 2) →* ℝˣ where
  toFun x := unit x.toAdd
  map_one' := unit_zero
  map_mul' x y := unit_add x.toAdd y.toAdd

theorem unit_eq_neg_one (x : ZMod 2) : (unit x : ℝ) = -1 ↔ x=1 := by
  fin_cases x <;> norm_num [unit]

variable {κ : Type*} [Fintype κ]

theorem monomial_sign (v : κ → ℤ) (x : κ → ZMod 2) :
    (∏ a, (unit (x a) : ℝ)^v a)=(unit (∑ a, (v a : ZMod 2)*x a) : ℝ) := by
  have h : (∏ a, unit (x a)^v a)=unit (∑ a, (v a : ZMod 2)*x a) := by
    change (∏ a, character (Multiplicative.ofAdd (x a))^v a)=
      character (Multiplicative.ofAdd (∑ a, (v a : ZMod 2)*x a))
    simp only [← zsmul_eq_mul,ofAdd_sum,ofAdd_zsmul,map_prod,map_zpow]
  exact_mod_cast h

theorem monomial_negative_iff (v : κ → ℤ) (x : κ → ZMod 2) :
    (∏ a, (unit (x a) : ℝ)^v a) = -1 ↔ ∑ a, (v a : ZMod 2)*x a=1 := by
  rw [monomial_sign,unit_eq_neg_one]

#print axioms unit
#print axioms unit_zero
#print axioms unit_one
#print axioms unit_add
#print axioms character
#print axioms unit_eq_neg_one
#print axioms monomial_sign
#print axioms monomial_negative_iff
end Verification.RealBitSigns
