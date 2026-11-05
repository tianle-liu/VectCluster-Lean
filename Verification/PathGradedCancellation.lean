/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathGradedMatrices
import Verification.FinitePerturbation

/-!
# Path Graded Cancellation

The finite geometric-series correction preserves the actual coefficient
grading, for all four matrices of the simultaneous contraction.
-/

namespace Verification.PathGradedCancellation

open Verification.PathCoefficientRing Verification.FinitePerturbation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (w : ι → ℤ) (A H V : Matrix ι ι Coeff)
variable (hA : PathGradedMatrices.Homogeneous w w A)
variable (hH : PathGradedMatrices.Homogeneous w w H)
variable (hV : PathGradedMatrices.Homogeneous w w V)

include hA hH in
theorem projection : PathGradedMatrices.Homogeneous w w (pureProjection A H) :=
  PathGradedMatrices.sub w w _ _ (PathGradedMatrices.sub w w _ _ (PathGradedMatrices.one w)
    (PathGradedMatrices.mul w w w A H hA hH)) (PathGradedMatrices.mul w w w H A hH hA)

include hH hV in
theorem inverse (n : ℕ) (hn : (V*H)^n=0) :
    PathGradedMatrices.Homogeneous w w (finiteUnit (V*H) n hn).inv := by
  change PathGradedMatrices.Homogeneous w w (∑ k∈Finset.range n, (-(V*H))^k)
  apply PathGradedMatrices.sum
  intro k _
  exact PathGradedMatrices.pow w _ (PathGradedMatrices.neg w w _
    (PathGradedMatrices.mul w w w V H hV hH)) k

variable (n : ℕ) (hn : (V*H)^n=0)

include hH hV in
theorem correction_degree : PathGradedMatrices.Homogeneous w w (correction V (finiteUnit (V*H) n hn)) :=
  PathGradedMatrices.mul w w w _ V (inverse w H V hH hV n hn) hV

include hH hV in
theorem homotopy : PathGradedMatrices.Homogeneous w w (correctedHomotopy H V (finiteUnit (V*H) n hn)) :=
  PathGradedMatrices.sub w w _ _ hH
    (PathGradedMatrices.mul w w w _ H
      (PathGradedMatrices.mul w w w H _ hH (correction_degree w H V hH hV n hn)) hH)

include hA hH hV in
theorem inclusion : PathGradedMatrices.Homogeneous w w (correctedInclusion A H V (finiteUnit (V*H) n hn)) :=
  PathGradedMatrices.sub w w _ _ (projection w A H hA hH)
    (PathGradedMatrices.mul w w w _ _
      (PathGradedMatrices.mul w w w H _ hH (correction_degree w H V hH hV n hn)) (projection w A H hA hH))

include hA hH hV in
theorem retraction : PathGradedMatrices.Homogeneous w w (correctedRetraction A H V (finiteUnit (V*H) n hn)) :=
  PathGradedMatrices.sub w w _ _ (projection w A H hA hH)
    (PathGradedMatrices.mul w w w _ H
      (PathGradedMatrices.mul w w w _ _ (projection w A H hA hH) (correction_degree w H V hH hV n hn)) hH)

include hA hH hV in
theorem residual : PathGradedMatrices.Homogeneous w w (residualDifferential A H V (finiteUnit (V*H) n hn)) :=
  PathGradedMatrices.mul w w w _ _
    (PathGradedMatrices.mul w w w _ _ (projection w A H hA hH) (correction_degree w H V hH hV n hn))
      (projection w A H hA hH)

#print axioms projection
#print axioms inverse
#print axioms correction_degree
#print axioms homotopy
#print axioms inclusion
#print axioms retraction
#print axioms residual

end Verification.PathGradedCancellation
