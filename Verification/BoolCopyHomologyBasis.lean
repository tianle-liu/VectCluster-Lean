/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.BoolMatrixCopies
import Mathlib.LinearAlgebra.Basis.Prod

/-!
# Bool Copy Homology Basis

Actual degreewise survivor and categorical homology bases of the two-copy
complex; their ranks are the sum of the two original ranks.
-/

namespace Verification.BoolCopyHomologyBasis

open Verification.GradedPerturbation Verification.FinitePerturbation
  Verification.PathPureContractionData Verification.PerturbedHomologyModel
  Verification.BoolMatrixCopies

variable {R : Type} [CommRing R]

noncomputable def boolCoordinates {M : Type} [AddCommGroup M] [Module R M] : (Bool → M) ≃ₗ[R] (M × M) where
  toFun f := (f false,f true)
  invFun x b := if b then x.2 else x.1
  left_inv f := by funext b; cases b <;> rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def fixedBasis (d : ι → ℤ) (P : Matrix ι ι R) (p : ℤ)
    {r : ℕ} (b : Basis (Fin r) R (fixedModule d P p)) :
    Basis (Fin (r+r)) R (fixedModule (fun x : Σ _ : Bool,ι => d x.2) (copy P) p) :=
  (((b.prod b).reindex finSumFinEquiv).map boolCoordinates.symm).map (fixedCoordinates d P p).symm

noncomputable def homologyBasis (d : ι → ℤ) (A : Matrix ι ι R) (T : Data d A)
    {r : ℕ} (b : Basis (Fin r) R ((matrixComplex d A T.differential_degree T.differential_square).homology 0)) :
    Basis (Fin (r+r)) R ((matrixComplex (fun x : Σ _ : Bool,ι => d x.2) (copy A)
      (contraction d A T).differential_degree (contraction d A T).differential_square).homology 0) := by
  let U := contraction d A T
  let bP := Verification.PathPureContractionData.homologyBasis d A T b
  let bQ := fixedBasis d (pureProjection A T.homotopy) 0 bP
  let E : fixedModule (fun x : Σ _ : Bool,ι => d x.2) (copy (pureProjection A T.homotopy)) 0 ≃ₗ[R]
      fixedModule (fun x : Σ _ : Bool,ι => d x.2) (pureProjection (copy A) U.homotopy) 0 :=
    LinearEquiv.ofEq _ _ (by rw [show U.homotopy=copy T.homotopy from rfl,copy_projection])
  exact (bQ.map E).map (Verification.PureDegreeSurvivors.pureHomologyIso _ _ U.homotopy
    U.differential_degree U.homotopy_degree U.differential_square U.homotopy_square
    U.homotopy_regular U.generalized 0).symm.toLinearEquiv

#print axioms boolCoordinates
#print axioms fixedBasis
#print axioms homologyBasis

end Verification.BoolCopyHomologyBasis
