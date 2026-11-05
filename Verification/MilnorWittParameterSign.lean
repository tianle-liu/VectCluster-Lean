/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.MilnorWittSymbolNaturality

/-!
# Milnor Witt Parameter Sign

Changing the genuine Laurent parameter by a power of -1 changes its
symbol contraction by the corresponding power of g. This accounts for the
literal x versus signed z normal parameter without any path-specific input.
-/
namespace Verification.MilnorWittParameterSign
open Verification.MilnorWittSymbolRelations Verification.MilnorWittSymbolNaturality
variable {S T A B : Type*} [CommRing S] [CommRing T] [Ring A] [Ring B]
variable (D₀ : Symbols S B) (D₁ : Symbols T A) (f : S →+* T) (F : B →+* A)
variable (h : Compatible D₀ D₁ f F)

include h in
theorem negative_normal_form (v : Tˣ) (b : B) :
    D₁.symbol (-v) * F b = F (D₀.rho*b) + D₁.symbol v * F (D₀.g*b) := by
  rw [D₁.negative,add_mul,map_mul,map_mul,h.rho,h.g]
  rw [(D₁.central_g (D₁.symbol v)).eq]
  simp only [mul_assoc]

include h in
theorem signed_parameter (u : Tˣ) (r : A →+ B)
    (r_constant : ∀ b,r (F b)=0) (r_parameter : ∀ b,r (D₁.symbol u * F b)=b)
    (n : ℕ) (b : B) : r (D₁.symbol ((-1 : Tˣ)^n * u) * F b) = D₀.g^n*b := by
  induction n generalizing b with
  | zero => simp only [pow_zero,one_mul,r_parameter]
  | succ n ih =>
    have hn : (-1 : Tˣ)^(n+1)*u = -((-1 : Tˣ)^n*u) := by
      rw [pow_succ',mul_assoc,neg_one_mul]
    rw [hn,negative_normal_form D₀ D₁ f F h,map_add,r_constant,zero_add,ih]
    rw [pow_succ,mul_assoc]

#print axioms negative_normal_form
#print axioms signed_parameter
end Verification.MilnorWittParameterSign
