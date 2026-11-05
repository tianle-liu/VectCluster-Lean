/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RealCharacterFibers

/-!
# Real Exchange Characters

Literal positive/negative exchange polynomials on real coordinates,
and their equivalence to the character equation on the torus.
-/
noncomputable section
namespace Verification.RealExchangeCharacters
variable {κ : Type*} [Fintype κ]

def exchange (x : κ → ℝ) (v : κ → ℤ) : ℝ :=
  (∏ a, x a^(v a).toNat)+(∏ a, x a^(-v a).toNat)

theorem power_factor (x : ℝ) (hx : x≠0) (v : ℤ) : x^v.toNat=x^(-v).toNat*x^v := by
  have h : (v.toNat:ℤ)=((-v).toNat:ℤ)+v := by omega
  rw [← zpow_natCast, h, zpow_add₀ hx,zpow_natCast]

theorem exchange_factor (x : κ → ℝ) (hx : ∀ a, x a≠0) (v : κ → ℤ) :
    exchange x v=(∏ a, x a^(-v a).toNat)*((∏ a, x a^v a)+1) := by
  unfold exchange
  simp_rw [power_factor (x _) (hx _) (v _)]
  rw [Finset.prod_mul_distrib]
  ring

theorem exchange_zero_iff (x : κ → ℝ) (hx : ∀ a, x a≠0) (v : κ → ℤ) :
    exchange x v=0 ↔ (∏ a, x a^v a)=-1 := by
  rw [exchange_factor x hx v]
  have hn : (∏ a, x a^(-v a).toNat)≠0 :=
    Finset.prod_ne_zero_iff.mpr (fun a _ => pow_ne_zero _ (hx a))
  rw [mul_eq_zero,or_iff_right hn]
  exact eq_neg_iff_add_eq_zero.symm

theorem exchange_continuous (v : κ → ℤ) : Continuous (fun x : κ → ℝ => exchange x v) :=
  (continuous_finset_prod _ (fun a _ => (continuous_apply a).pow _)).add
    (continuous_finset_prod _ (fun a _ => (continuous_apply a).pow _))

#print axioms exchange
#print axioms power_factor
#print axioms exchange_factor
#print axioms exchange_zero_iff
#print axioms exchange_continuous
end Verification.RealExchangeCharacters
