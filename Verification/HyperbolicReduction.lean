/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.Algebra
import Verification.PerturbedHomologyModel

/-!
# Hyperbolic Reduction

Specialization of the constructed finite cancellation to the manuscript's
literal ring R_h = Z[h]/(h²-2h).  The residual matrix is proved to be hA
for the displayed integer matrix A, and A²=0 is derived integrally.
-/

namespace Verification.HyperbolicReduction

open Verification.FinitePerturbation Verification.GradedPerturbation
open Verification.PerturbedHomologyModel
open Verification.Algebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Extension of the original integer matrices to the literal quotient ring. -/
noncomputable def castMatrix : Matrix ι ι ℤ →+* Matrix ι ι HyperbolicRing := integerMatrixMap

/-- The literal perturbation hV. -/
noncomputable def perturbation (V : Matrix ι ι ℤ) : Matrix ι ι HyperbolicRing := hyperbolic • castMatrix V

theorem cast_homogeneous (deg : ι → ℤ) (k : ℤ) (M : Matrix ι ι ℤ)
    (hM : Homogeneous deg k M) : Homogeneous deg k (castMatrix M) := by
  intro i j hij
  change (M i j : HyperbolicRing) = 0
  rw [hM i j hij, Int.cast_zero]

theorem perturbation_homogeneous (deg : ι → ℤ) (V : Matrix ι ι ℤ)
    (hV : Homogeneous deg 1 V) : Homogeneous deg 1 (perturbation V) := by
  intro i j hij
  change hyperbolic * (V i j : HyperbolicRing) = 0
  rw [hV i j hij, Int.cast_zero, mul_zero]

theorem cast_weight (H : Matrix ι ι ℤ) (w : ι → ℕ)
    (hH : ∀ i j, w i ≠ w j → H i j = 0) :
    ∀ i j, w i ≠ w j → castMatrix H i j = 0 := by
  intro i j hij
  change (H i j : HyperbolicRing) = 0
  rw [hH i j hij, Int.cast_zero]

theorem perturbation_weight (V : Matrix ι ι ℤ) (w : ι → ℕ)
    (hV : ∀ i j, w i ≤ w j → V i j = 0) :
    ∀ i j, w i ≤ w j → perturbation V i j = 0 := by
  intro i j hij
  change hyperbolic * (V i j : HyperbolicRing) = 0
  rw [hV i j hij, Int.cast_zero, mul_zero]

variable (U H V : Matrix ι ι ℤ)
variable (hU : U*U = 0) (hHH : H*H = 0) (hHUH : H*U*H = H) (hUHU : U*H*U = U)
variable (hD : (castMatrix U+perturbation V)*(castMatrix U+perturbation V) = 0)
variable (w : ι → ℕ) (b : ℕ) (hw : ∀ i, w i ≤ b)
variable (hH : ∀ i j, w i ≠ w j → H i j = 0)
variable (hV : ∀ i j, w i ≤ w j → V i j = 0)

/-- Actual simultaneous cancellation over R_h, with no new pivot assumption. -/
noncomputable def cancellationData :
    MatrixRetraction (castMatrix U+perturbation V) (pureProjection (castMatrix U) (castMatrix H)) :=
  filteredCancellation (castMatrix U) (castMatrix H) (perturbation V)
    (by rw [← map_mul, hU, map_zero]) (by rw [← map_mul, hHH, map_zero])
    (by rw [← map_mul, ← map_mul, hHUH]) (by rw [← map_mul, ← map_mul, hUHU])
    hD w b hw (cast_weight H w hH) (perturbation_weight V w hV)

/-- The actual remaining differential is h times the explicitly constructed integer path matrix. -/
theorem cancellation_differential :
    (cancellationData U H V hU hHH hHUH hUHU hD w b hw hH hV).differential =
      hyperbolicMatrix (integerResidual U H V (b+1)) := by
  have hs : hyperbolic*hyperbolic = 2*hyperbolic := by simpa only [pow_two] using hyperbolic_relation
  have hn := Verification.ChainCancellation.raising_matrix_nilpotent
    (perturbation V*castMatrix H) w b hw
    (preserving_raising_products (castMatrix H) (perturbation V) w
      (cast_weight H w hH) (perturbation_weight V w hV)).1
  exact finite_integral_hyperbolic_residual U H V hyperbolic hs (b+1) hn

include hU hHH hHUH hUHU hD hw hH hV in
/-- No division by h is used: the resulting integer matrix itself squares to zero. -/
theorem integer_residual_square :
    integerResidual U H V (b+1) * integerResidual U H V (b+1) = 0 := by
  apply hyperbolic_differential_detects_integer_complex
  rw [← cancellation_differential U H V hU hHH hHUH hUHU hD w b hw hH hV]
  exact (cancellationData U H V hU hHH hHUH hUHU hD w b hw hH hV).square

variable (deg : ι → ℤ)
variable (hdU : Homogeneous deg 1 U) (hdH : Homogeneous deg (-1) H) (hdV : Homogeneous deg 1 V)

/-- The degreewise retraction is derived over the same literal coefficient ring. -/
noncomputable def gradedData :
    GradedRetraction deg (castMatrix U+perturbation V) (pureProjection (castMatrix U) (castMatrix H)) :=
  filteredRetraction deg (castMatrix U) (castMatrix H) (perturbation V)
    (cast_homogeneous deg 1 U hdU) (cast_homogeneous deg (-1) H hdH) (perturbation_homogeneous deg V hdV)
    (by rw [← map_mul, hU, map_zero]) (by rw [← map_mul, hHH, map_zero])
    (by rw [← map_mul, ← map_mul, hHUH]) (by rw [← map_mul, ← map_mul, hUHU])
    hD w b hw (cast_weight H w hH) (perturbation_weight V w hV)

/-- The actual target cochain complex has the hA matrix just proved above. -/
theorem graded_differential :
    (gradedData U H V hU hHH hHUH hUHU hD w b hw hH hV deg hdU hdH hdV).differential =
      hyperbolicMatrix (integerResidual U H V (b+1)) :=
  cancellation_differential U H V hU hHH hHUH hUHU hD w b hw hH hV

/-- The constructed R_h reduction is an actual all-degree chain-homotopy equivalence. -/
noncomputable def reductionEquiv :
    HomotopyEquiv
      (sourceComplex deg _ _ (gradedData U H V hU hHH hHUH hUHU hD w b hw hH hV deg hdU hdH hdV))
      (targetComplex deg _ _ (gradedData U H V hU hHH hHUH hUHU hD w b hw hH hV deg hdU hdH hdV)) :=
  homotopyEquiv _ _ _ _

#print axioms castMatrix
#print axioms perturbation
#print axioms cast_homogeneous
#print axioms perturbation_homogeneous
#print axioms cast_weight
#print axioms perturbation_weight
#print axioms cancellationData
#print axioms cancellation_differential
#print axioms integer_residual_square
#print axioms gradedData
#print axioms graded_differential
#print axioms reductionEquiv

end Verification.HyperbolicReduction
