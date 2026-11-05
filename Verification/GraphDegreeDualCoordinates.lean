/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GraphChainMatrix
import Verification.IntegerGradedTransposeRank
import Verification.GraphTensorTF

/-!
# Graph Degree Dual Coordinates

Actual independence cochains in cardinal degree p identify with
the degree-p part of the literal transposed augmented chain matrix.
-/
noncomputable section
open scoped Classical
namespace Verification.GraphDegreeDualCoordinates
open CategoryTheory
open Verification.GraphCover Verification.GraphCoverGrading Verification.GraphChainMatrix
open Verification.GraphChainCochain
attribute [local instance 2000] ModuleCat.isModule
variable {V C : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) (c : V → C) (T : Finset V)

def degreeEquiv (p : ℕ) : (GraphTensorTF.integral G c T).X p ≃ₗ[ℤ]
    GradedPerturbation.degreeModule (R:=ℤ) (fun J=> -degree G T J) (p:ℤ) where
  toFun x := ⟨cochainCoordinates G c T x.val,by
    intro J hJ
    rw [cochainCoordinates_apply]
    apply (GraphBlockComplex.mem_degreeModule ℤ _ p x.val).mp x.property
    intro he
    apply hJ
    change -(-(J.val.card:ℤ))=(p:ℤ)
    change J.val.card=p at he
    simp [he]⟩
  invFun x := ⟨(cochainCoordinates G c T).symm x.val,by
    apply (GraphBlockComplex.mem_degreeModule ℤ _ p _).mpr
    intro J hJ
    have he : (cochainCoordinates G c T ((cochainCoordinates G c T).symm x.val))
        ((chainCochainIndex G c T).symm J)=x.val ((chainCochainIndex G c T).symm J) :=
      congrFun ((cochainCoordinates G c T).apply_symm_apply x.val) _
    rw [cochainCoordinates_apply,Equiv.apply_symm_apply] at he
    rw [he]
    apply x.property
    intro hd
    apply hJ
    change -(-(J.val.card:ℤ))=(p:ℤ) at hd
    change J.val.card=p
    omega⟩
  left_inv x := Subtype.ext ((cochainCoordinates G c T).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((cochainCoordinates G c T).apply_symm_apply x.val)
  map_add' x y := Subtype.ext (map_add _ x.val y.val)
  map_smul' r x := Subtype.ext (map_smul _ r x.val)

def dualComplex : CochainComplex (ModuleCat ℤ) ℤ :=
  GradedPerturbation.matrixComplex (fun J=> -degree G T J) (chainMatrix G T).transpose
    (TransposeReduction.homogeneous_transpose _ 1 _ (chainMatrix_degree G T))
    (by rw [← Matrix.transpose_mul,chainMatrix_square,Matrix.transpose_zero])

theorem differential (p q : ℕ) (hpq : p+1=q) (x : (GraphTensorTF.integral G c T).X p) :
    degreeEquiv G c T q ((GraphTensorTF.integral G c T).d p q x)=
      (dualComplex G T).d (p:ℤ) (q:ℤ) (degreeEquiv G c T p x) := by
  subst q
  change degreeEquiv G c T (p+1) ((GraphBlockComplex.simplexComplex ℤ G c (T,∅)).d p (p+1) x)=_
  simp only [GraphBlockComplex.simplexComplex,GraphBlockComplex.gradedComplex,CochainComplex.of_d]
  dsimp only [dualComplex]
  rw [PerturbedHomologyModel.matrixComplex_d _ _ _ _ (p:ℤ) ((p+1:ℕ):ℤ) (by omega)]
  apply Subtype.ext
  exact (LinearMap.congr_fun (cochainCoordinates_differential (R:=ℤ) G c T) x.val).symm

#print axioms degreeEquiv
#print axioms dualComplex
#print axioms differential
end Verification.GraphDegreeDualCoordinates
