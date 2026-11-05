/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.MilnorWittSymbolRelations

/-!
# Milnor Witt Signed Constants

The exact symbols of signed scalar units used at the path endpoints.
This is a consequence of the ordinary MW unit relations, including parity.
-/
namespace Verification.MilnorWittSignedConstants
open Verification.MilnorWittSymbolRelations
variable {S A : Type*} [CommRing S] [Ring A] (D : Symbols S A)

theorem negative_one : D.symbol (-1 : Sˣ)=D.rho := by
  rw [D.negative,D.one,mul_zero,add_zero]

theorem signed_power (n : ℕ) : D.symbol ((-1 : Sˣ)^n)=if n%2=0 then 0 else D.rho := by
  induction n with
  | zero => rw [pow_zero,D.one];rfl
  | succ n ih =>
    rw [pow_succ',neg_one_mul,D.negative,ih]
    by_cases hn : n%2=0
    · have hs : (n+1)%2≠0 := by omega
      rw [if_pos hn,if_neg hs,mul_zero,add_zero]
    · have hs : (n+1)%2=0 := by omega
      rw [if_neg hn,if_pos hs,D.g_rho,add_neg_cancel]

#print axioms negative_one
#print axioms signed_power
end Verification.MilnorWittSignedConstants
