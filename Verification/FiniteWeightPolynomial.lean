/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib

/-!
# Finite Weight Polynomial

Finite weight enumerators, with actual coefficient counts and the product
rule for arbitrary dependent choices.
-/
noncomputable section
namespace Verification.FiniteWeightPolynomial
open scoped BigOperators
open Polynomial Classical
variable {I : Type*} [Fintype I]
def polynomial (w : I→ℕ) : Polynomial ℕ := ∑ i,X^(w i)

theorem coefficient (w : I→ℕ) (j : ℕ) :
    (polynomial w).coeff j=(Finset.univ.filter (fun i=>w i=j)).card := by
  classical
  simp only [polynomial,Polynomial.finset_sum_coeff,Polynomial.coeff_X_pow,
    Finset.card_filter,eq_comm]

theorem product [DecidableEq I] {K : I→Type*} [∀i,Fintype (K i)] (w : ∀i,K i→ℕ) :
    polynomial (fun f : ∀i,K i=>∑i,w i (f i))=∏i,polynomial (w i) := by
  classical
  simp only [polynomial]
  simp_rw [←Finset.prod_pow_eq_pow_sum]
  exact (Fintype.prod_sum (fun i k=>(X:Polynomial ℕ)^(w i k))).symm

def bitWeight (b : Bool) : ℕ := if b then 1 else 0

theorem binary [DecidableEq I] : polynomial (fun f : I→Bool=>∑i,bitWeight (f i))=
    (1+(X:Polynomial ℕ))^Fintype.card I := by
  rw [product]
  simp [polynomial,Fintype.sum_bool,bitWeight,add_comm]

theorem cartesian {K : Type*} [Fintype K] (w : I→ℕ) (v : K→ℕ) :
    polynomial (fun x : I×K=>w x.1+v x.2)=polynomial w*polynomial v := by
  simp only [polynomial,Fintype.sum_prod_type,pow_add,Finset.sum_mul,Finset.mul_sum]
  exact Finset.sum_comm

#print axioms polynomial
#print axioms coefficient
#print axioms product
#print axioms bitWeight
#print axioms binary
#print axioms cartesian
end Verification.FiniteWeightPolynomial
