/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Milnor Witt Symbol Relations

Ordinary Milnor-Witt symbol relations, uniform in all units of a ring.
These are the standard coefficient and symbol identities supplied by the
external Milnor-Witt theory; no chart, matrix, cellular map, or model
identification occurs in this interface.
-/
namespace Verification.MilnorWittSymbolRelations
variable (S A : Type*) [CommRing S] [Ring A]

structure Coefficients (A : Type*) [Ring A] where
  g : A
  rho : A
  eta : A
  g_square : g*g=1
  g_rho : g*rho = -rho
  g_eta : g*eta = -eta
  eta_rho : eta*rho=g-1
  central_g : ∀ x, Commute g x
  central_rho : ∀ x, Commute rho x
  central_eta : ∀ x, Commute eta x

structure Symbols extends Coefficients A where
  symbol : Sˣ → A
  one : symbol 1=0
  product : ∀ a b, symbol (a*b)=symbol a+symbol b+eta*symbol a*symbol b
  negative : ∀ a, symbol (-a)=rho+g*symbol a
  inverse : ∀ a, symbol a⁻¹ = -g*symbol a
  square : ∀ a, symbol a*symbol a=rho*symbol a
  skew : ∀ a b, symbol a*symbol b = -g*(symbol b*symbol a)

namespace Coefficients
variable {A} (C : Coefficients A)

theorem g_g (x : A) : C.g*(C.g*x)=x := by rw [← mul_assoc,C.g_square,one_mul]

theorem g_rho_mul (x : A) : C.g*(C.rho*x)= -(C.rho*x) := by rw [← mul_assoc,C.g_rho,neg_mul]

theorem g_eta_mul (x : A) : C.g*(C.eta*x)= -(C.eta*x) := by rw [← mul_assoc,C.g_eta,neg_mul]

theorem eta_rho_mul (x : A) : C.eta*(C.rho*x)=C.g*x-x := by rw [← mul_assoc,C.eta_rho,sub_mul,one_mul]

theorem push_g (a x : A) : a*(C.g*x)=C.g*(a*x) := by rw [← mul_assoc,← (C.central_g a).eq,mul_assoc]

theorem push_rho (a x : A) : a*(C.rho*x)=C.rho*(a*x) := by rw [← mul_assoc,← (C.central_rho a).eq,mul_assoc]

theorem push_eta (a x : A) : a*(C.eta*x)=C.eta*(a*x) := by rw [← mul_assoc,← (C.central_eta a).eq,mul_assoc]

end Coefficients

namespace Symbols
variable {S A} (D : Symbols S A)

theorem square_tail (a : Sˣ) (x : A) : D.symbol a*(D.symbol a*x)=D.rho*(D.symbol a*x) := by
  rw [← mul_assoc,D.square,mul_assoc]

theorem swap_tail (a b : Sˣ) (x : A) :
    D.symbol a*(D.symbol b*x)= -D.g*(D.symbol b*(D.symbol a*x)) := by
  rw [← mul_assoc,D.skew]
  simp only [mul_assoc,neg_mul]

theorem negative_product (a b : Sˣ) :
    D.symbol (-(a*b))=D.rho+D.g*D.symbol a+D.g*D.symbol b+D.g*D.eta*D.symbol a*D.symbol b := by
  rw [D.negative,D.product]
  noncomm_ring

theorem negative_inverse (a : Sˣ) : D.symbol (-a⁻¹)=D.rho-D.symbol a := by
  rw [D.negative,D.inverse]
  simp only [mul_neg,neg_mul,← mul_assoc,D.g_square,one_mul,sub_eq_add_neg]

end Symbols
#print axioms Coefficients
#print axioms Symbols
#print axioms Coefficients.g_g
#print axioms Coefficients.g_rho_mul
#print axioms Coefficients.g_eta_mul
#print axioms Coefficients.eta_rho_mul
#print axioms Coefficients.push_g
#print axioms Coefficients.push_rho
#print axioms Coefficients.push_eta
#print axioms Symbols.square_tail
#print axioms Symbols.swap_tail
#print axioms Symbols.negative_product
#print axioms Symbols.negative_inverse
end Verification.MilnorWittSymbolRelations
