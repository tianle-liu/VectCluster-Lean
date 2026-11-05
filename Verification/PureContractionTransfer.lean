/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathPureContractionData
import Verification.BlockFixedCoordinates
import Verification.MatrixGeneralizedConjugation
import Verification.MatrixDegreeEquivalence

/-!
# Pure Contraction Transfer

The path induction data is invariant under an actual finite chain
coordinate change. Both the generalized inverse and all-degree vanishing
are transported by proved maps.
-/

namespace Verification.PureContractionTransfer

open CategoryTheory CategoryTheory.Limits Verification.GradedPerturbation
  Verification.FinitePerturbation Verification.PerturbedHomologyModel
  Verification.PathPureContractionData

variable {R ι κ : Type} [CommRing R]
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype κ] [DecidableEq κ] in
theorem vanishing (d : ι → ℤ) (D : Matrix ι ι R) (T : Data d D) (p : ℤ) (hp : p ≠ 0) :
    IsZero ((matrixComplex d D T.differential_degree T.differential_square).homology p) := by
  letI : Subsingleton (fixedModule d (pureProjection D T.homotopy) p) := ⟨fun x y =>
    (Verification.BlockFixedCoordinates.fixed_zero d _ T.supported p hp x).trans
      (Verification.BlockFixedCoordinates.fixed_zero d _ T.supported p hp y).symm⟩
  exact (Verification.PureDegreeSurvivors.pureHomologyIso d D T.homotopy
    T.differential_degree T.homotopy_degree T.differential_square T.homotopy_square
    T.homotopy_regular T.generalized p).isZero_iff.mpr (ModuleCat.isZero_of_subsingleton _)

noncomputable def transfer (d : ι → ℤ) (e : κ → ℤ) (E : (ι → R) ≃ₗ[R] (κ → R))
    (hE : ∀ p x,x ∈ degreeModule d p → E x ∈ degreeModule e p)
    (hI : ∀ p x,x ∈ degreeModule e p → E.symm x ∈ degreeModule d p)
    (A : Matrix ι ι R) (B : Matrix κ κ R) (hd : Homogeneous d 1 A) (hA : A*A=0)
    (h : (Matrix.toLin' B).comp E.toLinearMap=E.toLinearMap.comp (Matrix.toLin' A))
    (T : Data e B) : Data d A :=
  ofGeneralized d A (Verification.MatrixGeneralizedConjugation.transport E T.homotopy) hd hA
    (Verification.MatrixGeneralizedConjugation.generalized E A B T.homotopy h T.generalized)
    (fun p hp => (Verification.MatrixDegreeEquivalence.homologyIso d e E hE hI A B
      hd T.differential_degree hA T.differential_square h p).isZero_iff.mpr (vanishing e B T p hp))

#print axioms vanishing
#print axioms transfer

end Verification.PureContractionTransfer
