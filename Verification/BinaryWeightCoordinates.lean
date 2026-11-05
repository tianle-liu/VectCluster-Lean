/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GradedBinaryCoefficientTree
import Verification.FiniteWeightedTensor
import Verification.FiniteWeightPolynomial

/-!
# Binary Weight Coordinates

The actual recursive torus word indices are boolean choices on the
coordinate set, with their exact integral degree equal to the number of bits.
-/
noncomputable section
namespace Verification.BinaryWeightCoordinates
open Classical Verification.BinaryWordCoordinates
open scoped BigOperators

def finEquiv : ∀ n,Index n≃(Fin n→Bool)
  | 0=>{
      toFun:=fun _ i=>Fin.elim0 i
      invFun:=fun _=>PUnit.unit
      left_inv:=fun i=>by cases i;rfl
      right_inv:=fun _=>by funext i;exact Fin.elim0 i }
  | n+1=>(Equiv.prodCongr (Equiv.refl Bool) (finEquiv n)).trans
      (FiniteWeightedTensor.choiceEquiv (fun _ : Fin (n+1)=>Bool))

theorem fin_weight (n : ℕ) (i : Index n) :
    GradedBinaryCoefficientTree.weight n i=
      ((∑ j,FiniteWeightPolynomial.bitWeight (finEquiv n i j):ℕ):ℤ) := by
  induction n with
  | zero=>simp [GradedBinaryCoefficientTree.weight]
  | succ n ih=>
    rcases i with ⟨b,i⟩
    rw [Fin.sum_univ_succ]
    change GradedBinaryCoefficientTree.weight (n+1) (b,i)=
      ((FiniteWeightPolynomial.bitWeight b+∑ j : Fin n,FiniteWeightPolynomial.bitWeight (finEquiv n i j):ℕ):ℤ)
    cases b <;> simp [GradedBinaryCoefficientTree.weight,FiniteWeightPolynomial.bitWeight,ih]

variable (U : Type) [Fintype U]
def equiv : Index (Fintype.card U)≃(U→Bool) :=
  (finEquiv (Fintype.card U)).trans
    (Equiv.arrowCongr (Fintype.equivFin U).symm (Equiv.refl Bool))

theorem weight (i : Index (Fintype.card U)) :
    GradedBinaryCoefficientTree.weight (Fintype.card U) i=
      ((∑ u,FiniteWeightPolynomial.bitWeight (equiv U i u):ℕ):ℤ) := by
  rw [fin_weight]
  congr 1
  exact ((Fintype.equivFin U).sum_comp
    (fun j=>FiniteWeightPolynomial.bitWeight (finEquiv (Fintype.card U) i j))).symm

#print axioms finEquiv
#print axioms fin_weight
#print axioms equiv
#print axioms weight
end Verification.BinaryWeightCoordinates
