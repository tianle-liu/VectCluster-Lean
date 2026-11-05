/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathPureContractionData
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Pi

/-!
# Bool Matrix Copies

Two literal copies of a finite matrix and its normalized contraction,
indexed by the actual Bool sigma coordinates used by the Z open layer.
-/

namespace Verification.BoolMatrixCopies

open Verification.GradedPerturbation Verification.FinitePerturbation
  Verification.PathPureContractionData Verification.PerturbedHomologyModel

variable {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι]

def copy (A : Matrix ι ι R) : Matrix (Σ _ : Bool,ι) (Σ _ : Bool,ι) R :=
  Matrix.blockDiagonal' (fun _ : Bool => A)

omit [DecidableEq ι] in
theorem copy_mul (A B : Matrix ι ι R) : copy A*copy B=copy (A*B) :=
  (Matrix.blockDiagonal'_mul (fun _ : Bool => A) (fun _ : Bool => B)).symm

omit [Fintype ι] [DecidableEq ι] in
theorem copy_zero : copy (0 : Matrix ι ι R)=0 := Matrix.blockDiagonal'_zero

theorem copy_projection (A H : Matrix ι ι R) :
    pureProjection (copy A) (copy H)=copy (pureProjection A H) := by
  let f : Matrix ι ι R →+* Matrix (Σ _ : Bool,ι) (Σ _ : Bool,ι) R :=
    (Matrix.blockDiagonal'RingHom (fun _ : Bool => ι) R).comp (Pi.constRingHom Bool (Matrix ι ι R))
  change 1-f A*f H-f H*f A=f (1-A*H-H*A)
  rw [map_sub,map_sub,map_one,map_mul,map_mul]

omit [Fintype ι] [DecidableEq ι] in
theorem copy_degree (d : ι → ℤ) (k : ℤ) (A : Matrix ι ι R) (hd : Homogeneous d k A) :
    Homogeneous (fun x : Σ _ : Bool,ι => d x.2) k (copy A) := by
  intro ⟨i,x⟩ ⟨j,y⟩ hxy
  by_cases hij : i=j
  · subst j
    simpa only [copy,Matrix.blockDiagonal'_apply_eq] using hd x y hxy
  · exact Matrix.blockDiagonal'_apply_ne (fun _ : Bool => A) x y hij

noncomputable def contraction (d : ι → ℤ) (A : Matrix ι ι R) (T : Data d A) :
    Data (fun x : Σ _ : Bool,ι => d x.2) (copy A) where
  differential_degree := copy_degree d 1 A T.differential_degree
  differential_square := by rw [copy_mul,T.differential_square,copy_zero]
  homotopy := copy T.homotopy
  homotopy_degree := copy_degree d (-1) T.homotopy T.homotopy_degree
  homotopy_square := by rw [copy_mul,T.homotopy_square,copy_zero]
  homotopy_regular := by rw [copy_mul,copy_mul,T.homotopy_regular]
  generalized := by rw [copy_mul,copy_mul,T.generalized]
  supported := by
    intro ⟨i,x⟩ ⟨j,y⟩ hx
    rw [copy_projection]
    by_cases hij : i=j
    · subst j
      simpa only [copy,Matrix.blockDiagonal'_apply_eq] using T.supported x y hx
    · exact Matrix.blockDiagonal'_apply_ne (fun _ : Bool => pureProjection A T.homotopy) x y hij

omit [DecidableEq ι] in
theorem mulVec_apply (A : Matrix ι ι R) (x : (Σ _ : Bool,ι) → R) (b : Bool) (i : ι) :
    (copy A).mulVec x ⟨b,i⟩=A.mulVec (fun j => x ⟨b,j⟩) i := by
  simp [copy,Matrix.mulVec,dotProduct,Fintype.sum_sigma,Matrix.blockDiagonal'_apply]

noncomputable def fixedCoordinates (d : ι → ℤ) (P : Matrix ι ι R) (p : ℤ) :
    fixedModule (fun x : Σ _ : Bool,ι => d x.2) (copy P) p ≃ₗ[R] (Bool → fixedModule d P p) where
  toFun x b := ⟨fun i => x.val ⟨b,i⟩,(fun i hi => x.property.1 ⟨b,i⟩ hi),by
    funext i
    have hh := congrFun x.property.2 ⟨b,i⟩
    rw [mulVec_apply] at hh
    exact hh⟩
  invFun x := ⟨fun i => (x i.1).val i.2,by
    constructor
    · intro i hi; exact (x i.1).property.1 i.2 hi
    · funext i
      rw [mulVec_apply]
      exact congrFun (x i.1).property.2 i.2⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by funext b; apply Subtype.ext; rfl
  map_add' x y := by funext b; apply Subtype.ext; rfl
  map_smul' r x := by funext b; apply Subtype.ext; rfl

#print axioms copy
#print axioms copy_mul
#print axioms copy_zero
#print axioms copy_projection
#print axioms copy_degree
#print axioms contraction
#print axioms mulVec_apply
#print axioms fixedCoordinates

end Verification.BoolMatrixCopies
