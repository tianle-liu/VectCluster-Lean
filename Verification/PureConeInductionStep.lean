/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LowerConeRetraction
import Verification.BlockResidualBalance
import Verification.RecursiveResidualElimination

/-!
# Pure Cone Induction Step

The complete finite path-cone induction step over any commutative ring.
The two shorter contractions and three actual zeroth-homology bases determine
a contraction of the whole cone, once their proved ranks balance.
-/

namespace Verification.PureConeInductionStep

open Verification.GradedPerturbation Verification.FinitePerturbation
  Verification.PerturbedHomologyModel Verification.PathConeBlocks
  Verification.PathPureContractionData

variable {R ι κ : Type} [CommRing R]
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

noncomputable def step (a : ι → ℤ) (b : κ → ℤ)
    (A : Matrix ι ι R) (B : Matrix κ κ R) (C : Matrix κ ι R)
    (T : Data a A) (U : Data b B)
    (hd : Homogeneous (Verification.LowerConeRetraction.degree a b) 1 (Matrix.fromBlocks A 0 C B))
    (hD : Matrix.fromBlocks A 0 C B*Matrix.fromBlocks A 0 C B=0)
    {c m q : ℕ}
    (bA : Basis (Fin c) R ((matrixComplex a A T.differential_degree T.differential_square).homology 0))
    (bB : Basis (Fin m) R ((matrixComplex b B U.differential_degree U.differential_square).homology 0))
    (bD : Basis (Fin q) R ((matrixComplex (Verification.LowerConeRetraction.degree a b)
      (Matrix.fromBlocks A 0 C B) hd hD).homology 0)) (h : c+q=m) :
    Data (Verification.LowerConeRetraction.degree a b) (Matrix.fromBlocks A 0 C B) := by
  let d := Verification.LowerConeRetraction.degree a b
  let D := Matrix.fromBlocks A 0 C B
  let P := diagonal (pureProjection A T.homotopy) (pureProjection B U.homotopy)
  let F := Verification.LowerConeRetraction.ofBlocks a b A B C T U hd hD
  have hp : ∀ i j,d i ≠ -1 → d i ≠ 0 → P i j=0 :=
    Verification.BlockResidualBalance.diagonal_supported a b _ _ T.supported U.supported
  let bal : (fixedModule d P (-1) × (Fin q → R)) ≃ₗ[R] fixedModule d P 0 :=
    Verification.BlockResidualBalance.balance a b _ _ T.supported U.supported
      (homologyBasis a A T bA) (homologyBasis b B U bB) (Pi.basisFun R (Fin q)) h
  let H := Verification.RecursiveResidualElimination.contraction d D P F.toGradedRetraction
    F.projection_degree F.projection_square hp bD.equivFun bal
  exact {
    differential_degree := hd
    differential_square := hD
    homotopy := H
    homotopy_degree := Verification.RecursiveResidualElimination.contraction_degree d D P F.toGradedRetraction
      F.projection_degree F.projection_square hp bD.equivFun bal
    homotopy_square := Verification.RecursiveResidualElimination.contraction_square d D P F.toGradedRetraction
      F.projection_degree F.projection_square F.right_support hp bD.equivFun bal
    homotopy_regular := Verification.RecursiveResidualElimination.contraction_regular d D P F.toGradedRetraction
      F.projection_degree F.projection_square F.right_support hp bD.equivFun bal
    generalized := Verification.RecursiveResidualElimination.contraction_generalized d D P F.toGradedRetraction
      F.projection_degree F.projection_square F.right_support hp bD.equivFun bal
    supported := Verification.RecursiveResidualElimination.projection_supported d D P F.toGradedRetraction
      F.projection_degree F.projection_square F.right_support hp bD.equivFun bal }

#print axioms step

end Verification.PureConeInductionStep
