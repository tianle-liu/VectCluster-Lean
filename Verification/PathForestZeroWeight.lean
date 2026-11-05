/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathForestWeightPolynomial

/-!
# Path Forest Zero Weight

Exactly one forest survivor has weight zero; all others have positive
weight. Thus the constant summand remains a single copy of Z.
-/
noncomputable section
namespace Verification.PathForestZeroWeight
open Classical Verification.PathForestWeightPolynomial Verification.FiniteWeightPolynomial
variable {S : Type} [Fintype S] (U : Type) [Fintype U] (m : S→ℕ) (o : S→Bool)

theorem branch_zero (a : ℕ) (b : Bool) (x : Branch a b) :
    branchWeight a b x=0 ↔ x=none := by
  cases b <;> cases x <;> simp [branchWeight]

def zeroChoice : Choices U m o
  | none=>fun _=>false
  | some _=>none

omit [Fintype S] in
theorem factor_zero (j : Option S) (x : Choice U m o j) :
    factorWeight U m o j x=0 ↔ x=zeroChoice U m o j := by
  cases j with
  | none=>
    change (∑u,bitWeight (x u))=0 ↔ x=(fun _=>false)
    rw [Finset.sum_eq_zero_iff]
    simp only [Finset.mem_univ,true_implies]
    constructor
    · intro h
      funext u
      have hu := h u
      cases hx : x u <;> simp_all [bitWeight]
    · intro h
      rw [h]
      simp [bitWeight]
  | some s=>exact branch_zero (m s) (o s) x

theorem weight_zero (x : Choices U m o) :
    weight U m o x=0 ↔ x=zeroChoice U m o := by
  simp only [weight,Finset.sum_eq_zero_iff,Finset.mem_univ,true_implies,factor_zero]
  exact funext_iff.symm

theorem positive (x : Choices U m o) (hx : x≠zeroChoice U m o) :
    0<weight U m o x := Nat.pos_of_ne_zero (fun h=>hx ((weight_zero U m o x).mp h))

theorem constant_coefficient : (paperPolynomial U m o).coeff 0=1 := by
  rw [coefficient_count]
  have h : Finset.univ.filter (fun x : Choices U m o=>weight U m o x=0)={zeroChoice U m o} := by
    ext x
    simp [weight_zero]
  rw [h]
  rfl

#print axioms branch_zero
#print axioms zeroChoice
#print axioms factor_zero
#print axioms weight_zero
#print axioms positive
#print axioms constant_coefficient
end Verification.PathForestZeroWeight
