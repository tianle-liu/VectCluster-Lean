/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FiniteWeightPolynomial

/-!
# Path Forest Weight Polynomial

The finite survivor choices of a path forest have exactly the weight
polynomial P of the manuscript. Coefficients count actual choices.
-/
noncomputable section
namespace Verification.PathForestWeightPolynomial
open Classical Polynomial
open scoped BigOperators
open Verification.FiniteWeightPolynomial
variable {S : Type} [Fintype S] (U : Type) [Fintype U] (m : S→ℕ) (o : S→Bool)

def Branch (a : ℕ) (b : Bool) := Option (Fin (if b then 2*a+2 else a))
instance branchFintype (a : ℕ) (b : Bool) : Fintype (Branch a b) := inferInstanceAs (Fintype (Option _))
def branchWeight (a : ℕ) (b : Bool) : Branch a b→ℕ
  | none=>0
  | some k=>if b then k.val+1 else 2*(k.val+1)
def evenPolynomial (a : ℕ) : Polynomial ℕ := 1+∑ k : Fin a,X^(2*(k.val+1))
def oddPolynomial (a : ℕ) : Polynomial ℕ := 1+∑ k : Fin (2*a+2),X^(k.val+1)

theorem branch_polynomial (a : ℕ) (b : Bool) :
    polynomial (branchWeight a b)=if b then oddPolynomial a else evenPolynomial a := by
  cases b <;> simp [polynomial,Branch,branchWeight,Fintype.sum_option,evenPolynomial,oddPolynomial]

def Choice : Option S→Type
  | none=>U→Bool
  | some s=>Branch (m s) (o s)
instance choiceFintype (j : Option S) : Fintype (Choice U m o j) := by
  cases j <;> dsimp [Choice] <;> infer_instance

def factorWeight : ∀ j,Choice U m o j→ℕ
  | none,f=>∑u,bitWeight (f u)
  | some s,k=>branchWeight (m s) (o s) k
abbrev Choices := ∀j,Choice U m o j
def weight (x : Choices U m o) : ℕ := ∑j,factorWeight U m o j (x j)

def paperPolynomial : Polynomial ℕ :=
  (1+X)^Fintype.card U *
    (∏s ∈ Finset.univ.filter (fun s=>o s=false),evenPolynomial (m s)) *
    (∏s ∈ Finset.univ.filter (fun s=>o s=true),oddPolynomial (m s))

theorem generating_polynomial : polynomial (weight U m o)=paperPolynomial U m o := by
  change polynomial (fun x : Choices U m o=>∑j,factorWeight U m o j (x j))=_
  rw [product,Fintype.prod_option]
  change polynomial (fun f : U→Bool=>∑u,bitWeight (f u))*
    (∏s,polynomial (branchWeight (m s) (o s)))=_
  rw [binary]
  simp_rw [branch_polynomial]
  rw [Finset.prod_ite]
  have hf : Finset.univ.filter (fun s=>¬o s=true)=Finset.univ.filter (fun s=>o s=false) := by
    ext s;simp
  rw [hf]
  dsimp [paperPolynomial]
  ring

theorem coefficient_count (j : ℕ) :
    (paperPolynomial U m o).coeff j=(Finset.univ.filter (fun x : Choices U m o=>weight U m o x=j)).card := by
  rw [←generating_polynomial,coefficient]

#print axioms Branch
#print axioms branchFintype
#print axioms branchWeight
#print axioms evenPolynomial
#print axioms oddPolynomial
#print axioms branch_polynomial
#print axioms Choice
#print axioms choiceFintype
#print axioms factorWeight
#print axioms Choices
#print axioms weight
#print axioms paperPolynomial
#print axioms generating_polynomial
#print axioms coefficient_count
end Verification.PathForestWeightPolynomial
