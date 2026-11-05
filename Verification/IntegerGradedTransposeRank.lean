/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.IntegerDegreeMatrixRank

/-!
# Integer Graded Transpose Rank

A finite graded integer complex and its transposed dual have equal
homology ranks in opposite degrees. This statement retains the individual
degree and does not use a total-rank comparison.
-/
noncomputable section
open scoped Classical
namespace Verification.IntegerGradedTransposeRank
open Verification.GradedPerturbation
open Verification.IntegerDegreeMatrixRank
attribute [local instance 2000] ModuleCat.isModule
variable {ι : Type} [Fintype ι] (deg : ι → ℤ)

def negIndex (p : ℤ) : {i // -deg i= -p} ≃ {i // deg i=p} :=
  Equiv.subtypeEquivRight (fun _ => by omega)

theorem block_rank (D : Matrix ι ι ℤ) (p q : ℤ) :
    (block (fun i=> -deg i) D.transpose (-q) (-p)).rank=(block deg D p q).rank := by
  have he : block (fun i=> -deg i) D.transpose (-q) (-p)=
      (block deg D p q).transpose.submatrix (negIndex deg p) (negIndex deg q) := rfl
  rw [he,Matrix.rank_submatrix,IntegerMatrixRank.transpose]

theorem homology_rank (D : Matrix ι ι ℤ) (hD : Homogeneous deg 1 D) (hsq : D*D=0) (p : ℤ) :
    Module.finrank ℤ ((matrixComplex deg D hD hsq).homology p)=
      Module.finrank ℤ ((matrixComplex (fun i=> -deg i) D.transpose
        (TransposeReduction.homogeneous_transpose deg 1 D hD)
        (by rw [← Matrix.transpose_mul,hsq,Matrix.transpose_zero])).homology (-p)) := by
  have h₁ := balance deg D hD hsq p
  have h₂ := balance (fun i=> -deg i) D.transpose
    (TransposeReduction.homogeneous_transpose deg 1 D hD)
    (by rw [← Matrix.transpose_mul,hsq,Matrix.transpose_zero]) (-p)
  rw [show -p-1= -(p+1) by omega,show -p+1= -(p-1) by omega] at h₂
  rw [block_rank,block_rank,Fintype.card_congr (negIndex deg p)] at h₂
  omega

#print axioms negIndex
#print axioms block_rank
#print axioms homology_rank
end Verification.IntegerGradedTransposeRank
