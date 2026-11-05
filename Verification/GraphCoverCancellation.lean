/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GraphCoverProjection
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Graph Cover Cancellation

Actual finite cancellation of the augmented independence-chain complex along
a vertex cover. All matrix, nilpotence, grading and basis hypotheses are
verified on the explicit graph differential in preceding modules.
-/

namespace Verification.GraphCoverCancellation

open Classical
open CategoryTheory CategoryTheory.Limits
open Verification.GraphCover Verification.GraphCoverOrder
  Verification.GraphCoverMatrices Verification.GraphCoverGrading
  Verification.GraphCoverProjection Verification.GraphCoverBoundaryParts
  Verification.GradedPerturbation Verification.PerturbedHomologyModel

variable {R V : Type*} [CommRing R] [Fintype V] [LinearOrder V]
  (G : SimpleGraph V) (C T : Finset V) (hC : Covers G C) (hord : CoverOrdered C)

/-- Explicit finite geometric-series elimination of all nonempty outside fibers. -/
noncomputable def coverRetraction :
    GradedRetraction (degree G T)
      (outsideMatrix (R := R) G C T + coverMatrix G C T)
      (projectionMatrix G C T hC) := by
  have h := filteredRetraction (degree G T)
    (outsideMatrix (R := R) G C T) (contractionMatrix G C T hC) (coverMatrix G C T)
    (outsideMatrix_degree G C T) (contractionMatrix_degree G C T hC) (coverMatrix_degree G C T)
    (outsideMatrix_squared G C T hC hord) (contractionMatrix_squared G C T hC)
    (contractionMatrix_regular G C T hC hord) (outsideMatrix_regular G C T hC hord)
    (boundaryMatrix_squared G C T) (weight G C T) C.card
    (weight_bound G C T) (contractionMatrix_preserves_weight G C T hC) (coverMatrix_raises G C T)
  simpa only [Verification.FinitePerturbation.pureProjection,
    ← projectionMatrix_formula G C T hC hord] using h

/-- The source differential is literally the signed graph deletion matrix. -/
noncomputable def graphComplex : CochainComplex (ModuleCat R) ℤ :=
  sourceComplex _ _ _ (coverRetraction (R := R) G C T hC hord)

/-- The target uses precisely the dominating independent cover subsets as basis. -/
noncomputable def survivorComplex : CochainComplex (ModuleCat R) ℤ :=
  targetComplex _ _ _ (coverRetraction (R := R) G C T hC hord)

/-- A genuine chain homotopy equivalence, including the constructed finite homotopy. -/
noncomputable def coverHomotopyEquiv :
    HomotopyEquiv (graphComplex (R := R) G C T hC hord) (survivorComplex G C T hC hord) :=
  homotopyEquiv _ _ _ (coverRetraction G C T hC hord)

/-- Every target degree is finite free on explicitly specified original graph simplices. -/
noncomputable def survivorComplexBasis (p : ℤ) :
    Basis (SurvivorIndex G C T p) R ((survivorComplex (R := R) G C T hC hord).X p) :=
  survivorBasis G C T hC p

/-- Vanishing of a target degree requires only the absence of the actual survivor labels. -/
theorem survivorComplex_subsingleton (p : ℤ)
    (hempty : ∀ _ : SurvivorIndex G C T p, False) :
    Subsingleton ((survivorComplex (R := R) G C T hC hord).X p) := by
  letI : Subsingleton (SurvivorIndex G C T p → R) :=
    ⟨fun f g => funext (fun J => (hempty J).elim)⟩
  exact (fixedCoordinateEquiv (R := R) G C T hC p).injective.subsingleton

/-- The surviving free complex is concentrated in cochain degrees -a through zero,
equivalently augmented chain degrees -1 through a-1. -/
theorem survivorComplex_supported (p : ℤ) (hp : p < -(coverRank G C : ℤ) ∨ 0 < p) :
    Subsingleton ((survivorComplex (R := R) G C T hC hord).X p) := by
  apply survivorComplex_subsingleton G C T hC hord p
  intro J
  have h := survivor_degree_range G C T p J
  omega

/-- The same support statement holds for the actual categorical homology of the
original graph complex, transported through the constructed homotopy equivalence. -/
theorem graphHomology_zero_of_no_survivors (p : ℤ)
    (hempty : ∀ _ : SurvivorIndex G C T p, False) :
    IsZero ((graphComplex (R := R) G C T hC hord).homology p) := by
  letI := survivorComplex_subsingleton (R := R) G C T hC hord p hempty
  have hz : IsZero ((survivorComplex (R := R) G C T hC hord).homology p) := by
    apply HomologicalComplex.ExactAt.isZero_homology
    apply ShortComplex.exact_of_isZero_X₂
    change IsZero ((survivorComplex (R := R) G C T hC hord).X p)
    exact ModuleCat.isZero_of_subsingleton _
  exact ((coverHomotopyEquiv (R := R) G C T hC hord).toHomologyIso p).isZero_iff.mpr hz

#print axioms graphHomology_zero_of_no_survivors

#print axioms coverRetraction
#print axioms graphComplex
#print axioms survivorComplex
#print axioms coverHomotopyEquiv
#print axioms survivorComplexBasis
#print axioms survivorComplex_subsingleton
#print axioms survivorComplex_supported

end Verification.GraphCoverCancellation
