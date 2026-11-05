/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LaurentExchangeComponents
import Verification.PathForestOrientation
import Verification.PathForestComponentMatrix

/-!
# Path Forest Component Presentation

The normalized forest presentation separates into the actual
consecutive-path quotient rings over its Laurent coefficient algebra.
The block-diagonal identity is proved from the original parity matrix;
the resulting tensor-product isomorphism is constructed explicitly.
-/
noncomputable section
namespace Verification.PathForestComponentPresentation
open Classical Verification.PathForestFullRank Verification.PathForestComponentMatrix
open Verification.LaurentScalarModel
variable {S : Type} [Fintype S] (m : S → ℕ) (o : S → Bool)

abbrev Vertex := PathForestOrientation.Vertex m o
abbrev reindex := PathForestOrientation.reindex m o
abbrev blockMatrix := Matrix.blockDiagonal' (fun s => PathLattice.pathMatrix
  (PathOrientationBlocks.length (m s) (o s)))

theorem linear_reindex : (blockMatrix m o).submatrix (reindex m o) (reindex m o)=ordinaryMatrix m o := by
  have h := PathForestOrientation.matrix_reindex m o (fun _ _ => 1)
  have hm : PathForestOrientation.matrix m o (fun _ _ => 1)=blockMatrix m o := by
    change Matrix.blockDiagonal' _ = Matrix.blockDiagonal' _
    congr 1
  have hl : PathForestOrientation.leftSigns m o (fun _ _ => 1)=(fun _ _ => 1) := by
    funext s i
    simp [PathForestOrientation.leftSigns,PathOrientationBlocks.leftSign,PathOrientationSigns.vertexSign]
  have hr : PathForestOrientation.rightSigns m o (fun _ _ => 1)=(fun _ _ => 1) := by
    funext s i
    simp [PathForestOrientation.rightSigns,PathOrientationBlocks.rightSign,PathOrientationSigns.vertexSign]
  rw [hm,hl,hr] at h
  exact h

theorem principal_reindexed :
    (fun i j => ordinaryMatrix m o ((reindex m o).symm i) ((reindex m o).symm j)) = blockMatrix m o := by
  ext i j
  have h := congrFun (congrFun (linear_reindex m o) ((reindex m o).symm i)) ((reindex m o).symm j)
  simpa only [Matrix.submatrix_apply,Equiv.apply_symm_apply] using h.symm

variable (R : Type) [CommRing R] {M : Type} [AddCommGroup M]
variable (f : Vertices m o → M) (c : Vertices m o → Rˣ)

def consecutiveEquiv : Presentation R (ordinaryMatrix m o) f c ≃ₐ[R]
    Presentation R (blockMatrix m o) (fun v => f ((reindex m o).symm v))
      (fun v => c ((reindex m o).symm v)) :=
  (presentationEquiv R (reindex m o) (LinearEquiv.refl ℤ M) (ordinaryMatrix m o) f c).trans
    (Ideal.quotientEquivAlgOfEq R (congrArg (fun P => relations R P
      (fun v => f ((reindex m o).symm v)) (fun v => c ((reindex m o).symm v)))
        (principal_reindexed m o)))

attribute [local instance] MvPolynomial.algebraMvPolynomial

local instance ambientRing (α : Type) : CommRing (MvPolynomial α (MvPolynomial α (Coefficients R M))) := inferInstance

local instance componentRing (s : S) : CommRing (Presentation R
    (PathLattice.pathMatrix (PathOrientationBlocks.length (m s) (o s)))
    (fun i => f ((reindex m o).symm ⟨s,i⟩)) (fun i => c ((reindex m o).symm ⟨s,i⟩))) :=
  inferInstanceAs (CommRing (MvPolynomial (Fin (PathOrientationBlocks.length (m s) (o s)))
    (MvPolynomial (Fin (PathOrientationBlocks.length (m s) (o s))) (Coefficients R M)) ⧸
      relations R (PathLattice.pathMatrix (PathOrientationBlocks.length (m s) (o s)))
        (fun i => f ((reindex m o).symm ⟨s,i⟩)) (fun i => c ((reindex m o).symm ⟨s,i⟩))))

set_option synthInstance.maxHeartbeats 100000 in
def componentEquiv :=
  (consecutiveEquiv m o R f c).toRingEquiv.trans
    (LaurentExchangeComponents.separatedEquiv R
      (fun s => Fin (PathOrientationBlocks.length (m s) (o s)))
      (fun s => PathLattice.pathMatrix (PathOrientationBlocks.length (m s) (o s)))
      (fun s i => f ((reindex m o).symm ⟨s,i⟩))
      (fun s i => c ((reindex m o).symm ⟨s,i⟩))).toRingEquiv

#print axioms Vertex
#print axioms reindex
#print axioms blockMatrix
#print axioms linear_reindex
#print axioms principal_reindexed
#print axioms consecutiveEquiv
#print axioms ambientRing
#print axioms componentRing
#print axioms componentEquiv
end Verification.PathForestComponentPresentation
