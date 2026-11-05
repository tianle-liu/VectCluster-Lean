/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LSFourfoldSymbolProducts
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# LS Fourfold Symbol Words

All sixteen ordered subset words for each of the three concrete LS
substitutions, expanded into their ordinary Laurent constant and u-symbol parts.
-/
namespace Verification.LSFourfoldSymbolWords
open Verification.MilnorWittSymbolRelations Verification.LSFourfoldSymbolProducts
variable {S A : Type*} [CommRing S] [Ring A]

def coordinates (u a b : Sˣ) (j : Fin 3) : Fin 4 → Sˣ :=
  match j.val with
  | 0 => ![u,a,b,-(a*b)]
  | 1 => ![a,u,-a,b]
  | _ => ![a,-a⁻¹,u,b]

def word (x : Fin 4 → A) (s : Fin 16) : A := match s.val with
  | 0 => 1
  | 1 => x 0
  | 2 => x 1
  | 3 => x 0*x 1
  | 4 => x 2
  | 5 => x 0*x 2
  | 6 => x 1*x 2
  | 7 => x 0*x 1*x 2
  | 8 => x 3
  | 9 => x 0*x 3
  | 10 => x 1*x 3
  | 11 => x 0*x 1*x 3
  | 12 => x 2*x 3
  | 13 => x 0*x 2*x 3
  | 14 => x 1*x 2*x 3
  | _ => x 0*x 1*x 2*x 3

def residueTable (D : Symbols S A) (a b : Sˣ) (j : Fin 3) (s : Fin 16) : A :=
  match j.val,s.val with
  | 0,1 => 1
  | 0,3 => D.symbol a
  | 0,5 => D.symbol b
  | 0,7 => D.symbol a*D.symbol b
  | 0,9 => D.rho+D.g*D.symbol a+D.g*D.symbol b+D.g*D.eta*D.symbol a*D.symbol b
  | 0,11 => D.symbol a*D.symbol b
  | 0,13 => -D.g*(D.symbol a*D.symbol b)
  | 0,15 => D.rho*(D.symbol a*D.symbol b)
  | 1,2 => 1
  | 1,3 => -D.g*D.symbol a
  | 1,6 => D.rho+D.g*D.symbol a
  | 1,10 => D.symbol b
  | 1,11 => -D.g*(D.symbol a*D.symbol b)
  | 1,14 => D.rho*D.symbol b+D.g*(D.symbol a*D.symbol b)
  | 2,4 => 1
  | 2,5 => -D.g*D.symbol a
  | 2,6 => D.rho+D.g*D.symbol a
  | 2,12 => D.symbol b
  | 2,13 => -D.g*(D.symbol a*D.symbol b)
  | 2,14 => D.rho*D.symbol b+D.g*(D.symbol a*D.symbol b)
  | _,_ => 0

theorem word_normal_form (D : Symbols S A) (u a b : Sˣ) (j : Fin 3) (s : Fin 16) :
    word (fun i => D.symbol (coordinates u a b j i)) s =
      word (fun i => D.symbol (coordinates 1 a b j i)) s+
        D.symbol u*residueTable D a b j s := by
  fin_cases j <;> fin_cases s <;> dsimp [word,coordinates,residueTable,Matrix.cons_val]
  all_goals simp only [D.one,zero_mul,mul_zero,zero_add,add_zero,mul_one]
  all_goals noncomm_ring [D.negative, D.product, D.inverse, D.negative_product, D.negative_inverse, (D.toCoefficients.push_g (D.symbol a)), (D.toCoefficients.push_g (D.symbol b)), (D.toCoefficients.push_g (D.symbol u)), (D.toCoefficients.push_rho (D.symbol a)), (D.toCoefficients.push_rho (D.symbol b)), (D.toCoefficients.push_rho (D.symbol u)), (D.toCoefficients.push_eta (D.symbol a)), (D.toCoefficients.push_eta (D.symbol b)), (D.toCoefficients.push_eta (D.symbol u)), (D.toCoefficients.push_g D.eta), ← (D.central_rho (D.symbol a)).eq, ← (D.central_rho (D.symbol b)).eq, ← (D.central_rho (D.symbol u)).eq, D.square, (D.square_tail a), (D.square_tail b), (D.skew b a), (D.swap_tail b a), (D.skew a u), (D.swap_tail a u), D.toCoefficients.g_g, D.toCoefficients.g_rho_mul, D.toCoefficients.g_eta_mul, D.toCoefficients.eta_rho_mul]

#print axioms coordinates
#print axioms word
#print axioms residueTable
#print axioms word_normal_form
end Verification.LSFourfoldSymbolWords
