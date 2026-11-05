/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathRhoWords

/-!
# Path Word Column Formula

Closed formula for the existing full-rho word-column operator: all prefix
signs and the unique surviving compressed word are retained literally.
-/
noncomputable section
namespace Verification.PathWordColumnFormula
open Verification.PathRhoFaces Verification.PathRhoWords
variable {R : Type*} [CommRing R]

def phaseProduct (ε : R) : List Bool → R
  | [] => 1
  | a::xs => phase ε a * phaseProduct ε xs

theorem column (ε ρ : R) (pre tail : List Bool) (a b c : Bool) :
    faceColumn ε ρ pre.length (pre ++ a::b::c::tail) =
      if b then (phaseProduct ε pre * (phase ε a * repeatFactor ρ a c)) •
        Finsupp.single (pre ++ (a || c)::tail) 1 else 0 := by
  induction pre with
  | nil => simp only [List.length_nil,List.nil_append,phaseProduct,one_mul,faceColumn]
  | cons x xs ih =>
    simp only [List.length_cons,List.cons_append,faceColumn,ih,phaseProduct]
    cases b <;> simp only [Bool.false_eq_true,↓reduceIte,map_zero,smul_zero,
      map_smul,prepend_single,smul_smul,mul_assoc]

#print axioms phaseProduct
#print axioms column
end Verification.PathWordColumnFormula
