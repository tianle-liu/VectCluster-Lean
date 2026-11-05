/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GraphTensorTF
import Verification.GraphChainTF

/-!
# Graph Tensor TF From Chain

The article's original all-induced chain-freeness condition supplies
both adjacent cohomology TF hypotheses in the actual coefficient formula.
-/
noncomputable section
open scoped Classical
namespace Verification.GraphTensorTFFromChain
attribute [local instance 2000] ModuleCat.isModule
variable {V C : Type} [Fintype V] [Fintype C] [LinearOrder V] [LinearOrder C]
variable (G : SimpleGraph V) (c : V → C)

include c in
omit [Fintype C] in
theorem integral_tf (h : GraphChainTF.ChainGraphFree G) (T : Finset V) (p : ℕ) :
    NoZeroSMulDivisors ℤ ((GraphTensorTF.integral G c T).homology p) := by
  have ht := GraphChainTF.cochainGraphTF_of_chainFree G c h T p
  have he : (fun a b : C => Classical.propDecidable (a=b)) =
      (fun a b : C => LinearOrder.toDecidableEq a b) := Subsingleton.elim _ _
  rw [← he] at ht
  constructor
  intro a x hx
  exact ht.eq_zero_or_eq_zero_of_smul_eq_zero
    ((int_smul_eq_zsmul (ModuleCat.isModule ((GraphTensorTF.integral G c T).homology p)) a x).trans hx)

def coefficientEquiv (h : GraphChainTF.ChainGraphFree G) (T : Finset V)
    (A : Type) [AddCommGroup A] (p : ℕ) (hp : 0 < p) :
    (GraphTensorCohomology.simplex G c A (T,∅)).homology p ≃+
      (Fin (GraphTensorTF.betti G c T p) → A) :=
  GraphTensorTF.coefficientEquiv G c T A p hp
    (integral_tf G c h T p) (integral_tf G c h T (p+1))

#print axioms integral_tf
#print axioms coefficientEquiv
end Verification.GraphTensorTFFromChain
