/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.MilnorWittSymbolRelations

/-!
# LS Fourfold Symbol Products

The noncommutative Milnor-Witt products required by the three literal LS
coordinate substitutions. These calculations use only ordinary uniform symbol
relations; the identities are conclusions, not selected-chart hypotheses.
-/
namespace Verification.LSFourfoldSymbolProducts
open Verification.MilnorWittSymbolRelations
variable {S A : Type*} [CommRing S] [Ring A]
variable (D : Symbols S A) (a b : Sˣ)

local notation "aa" => D.symbol a
local notation "bb" => D.symbol b

lemma a_negative_a : aa*D.symbol (-a)=0 := by
  rw [D.negative]
  noncomm_ring [D.toCoefficients.push_g aa,← (D.toCoefficients.central_rho aa).eq,D.square,
    D.toCoefficients.g_rho_mul]

lemma a_negative_inverse : aa*D.symbol (-a⁻¹)=0 := by
  rw [D.negative_inverse]
  noncomm_ring [← (D.toCoefficients.central_rho aa).eq,D.square]

lemma a_negative_product : aa*D.symbol (-(a*b))=aa*bb := by
  rw [D.negative_product]
  noncomm_ring [D.toCoefficients.push_g aa,D.toCoefficients.push_eta aa,← (D.toCoefficients.central_rho aa).eq,
    D.square,D.square_tail a,D.toCoefficients.g_rho_mul,D.toCoefficients.eta_rho_mul,D.toCoefficients.g_g]

lemma b_negative_product : bb*D.symbol (-(a*b))= -D.g*(aa*bb) := by
  rw [D.negative_product]
  noncomm_ring [D.toCoefficients.push_g bb,D.toCoefficients.push_eta bb,← (D.toCoefficients.central_rho bb).eq,
    D.square,D.square_tail b,D.skew b a,D.swap_tail b a,
    D.toCoefficients.g_rho_mul,D.toCoefficients.eta_rho_mul,D.toCoefficients.g_g,D.toCoefficients.g_eta_mul,D.toCoefficients.push_g D.eta,D.toCoefficients.push_rho aa]

lemma ab_negative_product : (aa*bb)*D.symbol (-(a*b))=D.rho*(aa*bb) := by
  rw [mul_assoc,b_negative_product D a b]
  simp only [neg_mul,mul_neg,D.toCoefficients.push_g aa,D.square_tail a,D.toCoefficients.g_rho_mul,neg_neg]

#print axioms a_negative_a
#print axioms a_negative_inverse
#print axioms a_negative_product
#print axioms b_negative_product
#print axioms ab_negative_product
end Verification.LSFourfoldSymbolProducts
