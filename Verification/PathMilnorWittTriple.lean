/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.MilnorWittSymbolNaturality
import Verification.PathRhoFaces

/-!
# Path Milnor Witt Triple

Actual unit symbols on an ordinary Laurent line give the local full-rho
path face. Only uniform Milnor-Witt identities and the ordinary constant /
parameter contraction rules are used; no path differential is an input.
-/
namespace Verification.PathMilnorWittTriple
open Verification.MilnorWittSymbolRelations Verification.MilnorWittSymbolNaturality
variable {S T A B : Type*} [CommRing S] [CommRing T] [Ring A] [Ring B]

def bit {C : Type*} [One C] (x : C) (b : Bool) : C := if b then x else 1

def word {C : Type*} [Monoid C] (a u b : C) (w : Verification.PathRhoFaces.Triple) : C :=
  bit a w.1 * bit u w.2.1 * bit b w.2.2

def residue (D : Symbols S B) (a : Sˣ) (w : Verification.PathRhoFaces.Triple) : B :=
  if w.2.1 then (if w.1 then -D.g else 1) * (if w.1 && w.2.2 then D.rho else 1) *
    bit (D.symbol a) (w.1 || w.2.2) else 0

variable (D₀ : Symbols S B) (D₁ : Symbols T A) (f : S →+* T) (F : B →+* A)
variable (h : Compatible D₀ D₁ f F) (u : Tˣ) (a : Sˣ)

include h in
theorem swap_parameter :
    D₁.symbol (Units.map f.toMonoidHom a) * D₁.symbol u =
    D₁.symbol u * F (-D₀.g * D₀.symbol a) := by
  rw [map_mul,map_neg,h.g,h.symbol,D₁.skew]
  simp only [neg_mul,mul_neg,← mul_assoc]
  rw [(D₁.central_g (D₁.symbol u)).eq]

include h in
theorem normal_form (w : Verification.PathRhoFaces.Triple) :
    word (D₁.symbol (Units.map f.toMonoidHom a)) (D₁.symbol u)
      (D₁.symbol (Units.map f.toMonoidHom a)) w =
    F (word (D₀.symbol a) 0 (D₀.symbol a) w) +
      D₁.symbol u * F (residue D₀ a w) := by
  rcases w with ⟨l,m,r⟩
  cases l <;> cases m <;> cases r <;>
    simp only [word,bit,residue,Bool.false_eq_true,↓reduceIte,Bool.false_and,Bool.true_and,
      Bool.false_or,Bool.true_or,map_mul,map_zero,map_one,map_neg,h.g,h.rho,h.symbol,
      one_mul,mul_one,zero_mul,mul_zero,zero_add,add_zero]
  · simpa only [map_mul,map_neg,h.g,h.symbol] using swap_parameter D₀ D₁ f F h u a
  · rw [swap_parameter D₀ D₁ f F h u a,map_mul,map_neg,h.g,h.symbol]
    simp only [mul_assoc]
    rw [D₁.square]

include h in
theorem contraction (r : A →+ B) (r_constant : ∀ b,r (F b)=0)
    (r_parameter : ∀ b,r (D₁.symbol u * F b)=b)
    (w : Verification.PathRhoFaces.Triple) :
    r (word (D₁.symbol (Units.map f.toMonoidHom a)) (D₁.symbol u)
      (D₁.symbol (Units.map f.toMonoidHom a)) w) = residue D₀ a w := by
  rw [normal_form D₀ D₁ f F h u a,map_add,r_constant,r_parameter,zero_add]

#print axioms bit
#print axioms word
#print axioms residue
#print axioms swap_parameter
#print axioms normal_form
#print axioms contraction
end Verification.PathMilnorWittTriple
