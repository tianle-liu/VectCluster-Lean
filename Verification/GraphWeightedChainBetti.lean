/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GraphChainCochainBetti
import Verification.GraphTensorTFFreeFamily

/-!
# Graph Weighted Chain Betti

The literal weighted exponent is written using the actual reduced
chain-homology Betti numbers, degree by degree, as in the manuscript.
-/
noncomputable section
open scoped Classical
namespace Verification.GraphWeightedChainBetti
attribute [local instance 2000] ModuleCat.isModule
variable {V C : Type} [Fintype V] [Fintype C] [LinearOrder V] [LinearOrder C]
variable (G : SimpleGraph V) (c : V → C)

def exponent (p : ℕ) : ℕ := ∑ T : Finset V, GraphBlockMultiplicity.multiplicity c T *
  Module.finrank ℤ ((GraphChainMatrix.chainComplex (R := ℤ) G T).homology (-(p : ℤ)))

theorem rank_eq (p : ℕ) (hp : 0 < p) : GraphTensorTFFreeFamily.rank G c p = exponent G c p := by
  apply Finset.sum_congr rfl
  intro T _
  rw [GraphChainCochainBetti.betti G c T p hp]

variable (A : Type) [AddCommGroup A]
def coefficientEquiv (h : GraphChainTF.ChainGraphFree G) (p : ℕ) (hp : 0 < p) :
    ((T : Finset V) → Fin (GraphBlockMultiplicity.multiplicity c T) →
      (GraphTensorCohomology.simplex G c A (T,∅)).homology p) ≃+ (Fin (exponent G c p) → A) :=
  (GraphTensorTFFreeFamily.coefficientEquiv G c p A h hp).trans
    (LinearEquiv.piCongrLeft' ℤ (fun _ => A) (finCongr (rank_eq G c p hp))).toAddEquiv

#print axioms exponent
#print axioms rank_eq
#print axioms coefficientEquiv
end Verification.GraphWeightedChainBetti
