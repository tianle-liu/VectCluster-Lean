/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.HyperbolicReduction
import Verification.GradedIntegralSplitting
import Verification.GradedSurvivorBasis

/-!
# TF Even Reduction

A single constructed TF-to-hA reduction over the literal hyperbolic ring.
The input records an actual finite graded integer differential and its filtered
perturbation.  Its TF input is actual degreewise categorical homology; neither
a contraction, survivor basis, nor residual differential is an input.
-/

namespace Verification.TFEvenReduction

open Verification.Algebra Verification.FinitePerturbation
open Verification.GradedPerturbation Verification.HyperbolicReduction
open Verification.PerturbedHomologyModel Verification.GradedIntegralSplitting

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Checkable original-matrix inputs to the even reduction, before cancellation. -/
structure Input where
  pure : Matrix ι ι ℤ
  perturb : Matrix ι ι ℤ
  degree : ι → ℤ
  weight : ι → ℕ
  bound : ℕ
  pure_square : pure*pure=0
  full_square : (castMatrix pure+perturbation perturb)*(castMatrix pure+perturbation perturb)=0
  pure_degree : Homogeneous degree 1 pure
  perturb_degree : Homogeneous degree 1 perturb
  pure_weight : ∀ i j, weight i ≠ weight j → pure i j=0
  perturb_weight : ∀ i j, weight i ≤ weight j → perturb i j=0
  weight_bound : ∀ i, weight i ≤ bound
  tf : ∀ p, NoZeroSMulDivisors ℤ ((matrixComplex degree pure pure_degree pure_square).homology p)

variable (T : Input (ι := ι))

/-- Degreewise TF supplies the exact total quotient required by the splitting constructor. -/
theorem total_tf : NoZeroSMulDivisors ℤ
    (Verification.IntegralSplitting.Homology (Matrix.toLin' T.pure)) := by
  apply Verification.GradedHomologyTF.total_tf T.degree T.pure T.pure_degree T.pure_square
  intro p
  letI : SMul ℤ ((matrixComplex T.degree T.pure T.pure_degree T.pure_square).homology p) :=
    (ModuleCat.isModule ((matrixComplex T.degree T.pure T.pure_degree T.pure_square).homology p)).toSMul
  constructor
  intro a x hx
  exact (T.tf p).eq_zero_or_eq_zero_of_smul_eq_zero
    ((int_smul_eq_zsmul (ModuleCat.isModule
      ((matrixComplex T.degree T.pure T.pure_degree T.pure_square).homology p)) a x).symm.trans hx)

/-- The contraction is constructed internally from TF and corrected to both gradings. -/
noncomputable def contraction : Matrix ι ι ℤ := by
  letI := total_tf T
  exact tfContraction T.pure T.pure_square T.degree (fun i => (T.weight i : ℤ))

theorem pure_weight_int : Homogeneous (fun i => (T.weight i : ℤ)) 0 T.pure := by
  intro i j hij
  exact T.pure_weight i j (by intro he; simp [he] at hij)

theorem contraction_square : contraction T*contraction T=0 := by
  letI := total_tf T
  exact tfContraction_square T.pure T.pure_square T.degree _ T.pure_degree (pure_weight_int T)

theorem contraction_generalized : T.pure*contraction T*T.pure=T.pure := by
  letI := total_tf T
  exact tfContraction_generalized T.pure T.pure_square T.degree _ T.pure_degree (pure_weight_int T)

theorem contraction_regular : contraction T*T.pure*contraction T=contraction T := by
  letI := total_tf T
  exact tfContraction_regular T.pure T.pure_square T.degree _ T.pure_degree (pure_weight_int T)

theorem contraction_degree : Homogeneous T.degree (-1) (contraction T) := by
  letI := total_tf T
  exact tfContraction_degree T.pure T.pure_square T.degree _ T.pure_degree

theorem contraction_weight : ∀ i j, T.weight i ≠ T.weight j → contraction T i j=0 := by
  letI := total_tf T
  have hh := tfContraction_weight T.pure T.pure_square T.degree _ (pure_weight_int T)
  intro i j hij
  exact hh i j (by simp only [add_zero]; exact_mod_cast hij)

/-- The original integral homology projection for this internally constructed contraction. -/
noncomputable def projection : Matrix ι ι ℤ := pureProjection T.pure (contraction T)

theorem projection_square : projection T*projection T=projection T :=
  pureProjection_square _ _ T.pure_square (contraction_square T)
    (contraction_regular T) (contraction_generalized T)

theorem projection_degree : Homogeneous T.degree 0 (projection T) := by
  have h1 : Homogeneous T.degree 0 (T.pure*contraction T) := by
    simpa using homogeneous_mul T.degree 1 (-1) _ _ T.pure_degree (contraction_degree T)
  have h2 : Homogeneous T.degree 0 (contraction T*T.pure) := by
    simpa using homogeneous_mul T.degree (-1) 1 _ _ (contraction_degree T) T.pure_degree
  exact homogeneous_sub T.degree 0 _ _
    (homogeneous_sub T.degree 0 _ _ (homogeneous_one T.degree) h1) h2

/-- Every corrected matrix and homotopy is obtained from finite filtered cancellation. -/
noncomputable def retractionData :
    GradedRetraction T.degree (castMatrix T.pure+perturbation T.perturb)
      (pureProjection (castMatrix T.pure) (castMatrix (contraction T))) :=
  gradedData T.pure (contraction T) T.perturb T.pure_square (contraction_square T)
    (contraction_regular T) (contraction_generalized T) T.full_square
    T.weight T.bound T.weight_bound (contraction_weight T) T.perturb_weight
    T.degree T.pure_degree (contraction_degree T) T.perturb_degree

/-- The integral path-sum differential, with the finite length bound built in. -/
noncomputable def integerDifferential : Matrix ι ι ℤ :=
  integerResidual T.pure (contraction T) T.perturb (T.bound+1)

/-- The actual residual operator is hA, for the displayed integer matrix. -/
theorem residual_hA : (retractionData T).differential=hyperbolicMatrix (integerDifferential T) :=
  graded_differential T.pure (contraction T) T.perturb T.pure_square (contraction_square T)
    (contraction_regular T) (contraction_generalized T) T.full_square
    T.weight T.bound T.weight_bound (contraction_weight T) T.perturb_weight
    T.degree T.pure_degree (contraction_degree T) T.perturb_degree

/-- The constructed integer differential itself squares to zero. -/
theorem integer_square : integerDifferential T*integerDifferential T=0 :=
  integer_residual_square T.pure (contraction T) T.perturb T.pure_square (contraction_square T)
    (contraction_regular T) (contraction_generalized T) T.full_square
    T.weight T.bound T.weight_bound (contraction_weight T) T.perturb_weight

/-- The integer residual has degree one, detected from its literal h multiple. -/
theorem integer_degree : Homogeneous T.degree 1 (integerDifferential T) := by
  intro i j hij
  have hz := (retractionData T).degreeS i j hij
  rw [residual_hA T] at hz
  have he := congrArg evaluateAtTwo hz
  simp only [hyperbolicMatrix, map_mul, evaluate_hyperbolic, map_intCast, map_zero] at he
  norm_num at he
  exact he

/-- The integer residual lands in the original integral survivor lattice. -/
theorem integer_support : projection T*integerDifferential T=integerDifferential T := by
  change projection T*(projection T*_ *projection T)=projection T*_ *projection T
  rw [← mul_assoc, ← mul_assoc, projection_square T]

/-- The reduced integral chain complex itself, on the actual integral survivor lattices. -/
noncomputable def integerComplex : CochainComplex (ModuleCat ℤ) ℤ :=
  fixedComplex T.degree (projection T) (integerDifferential T)
    (integer_degree T) (integer_support T) (integer_square T)

/-- Explicit finite integral basis in each degree of the integer residual complex. -/
noncomputable def integerBasis (p : ℤ) :
    Basis (Fin (Module.finrank ℤ (Verification.SurvivorBaseChange.fixedModule
      (Verification.GradedSurvivorBasis.cut T.degree p (projection T)))))
      ℤ ((integerComplex T).X p) :=
  (Verification.GradedSurvivorBasis.integralDegreeBasis T.degree (projection T) p).map
    (LinearEquiv.ofEq _ _ (Verification.GradedSurvivorBasis.fixedModule_cut
      T.degree (projection T) (projection_degree T) p))

/-- The actual source complex and exact residual survivor complex are homotopy equivalent. -/
noncomputable def equivalence :
    HomotopyEquiv (sourceComplex T.degree _ _ (retractionData T))
      (targetComplex T.degree _ _ (retractionData T)) :=
  homotopyEquiv _ _ _ _

/-- Coefficient extension commutes with the exact integer survivor projection. -/
theorem cast_projection : (projection T).map (Int.castRingHom HyperbolicRing) =
    pureProjection (castMatrix T.pure) (castMatrix (contraction T)) := by
  change castMatrix (pureProjection T.pure (contraction T)) = _
  simp only [pureProjection, map_sub, map_one, map_mul]

/-- Every actual degree of the reduced complex has this constructed finite free basis. -/
noncomputable def targetBasis (p : ℤ) :
    Basis (Fin (Module.finrank ℤ (Verification.SurvivorBaseChange.fixedModule
      (Verification.GradedSurvivorBasis.cut T.degree p (projection T)))))
      HyperbolicRing ((targetComplex T.degree _ _ (retractionData T)).X p) := by
  change Basis _ HyperbolicRing
    (fixedModule T.degree (pureProjection (castMatrix T.pure) (castMatrix (contraction T))) p)
  exact (Verification.GradedSurvivorBasis.scalarDegreeBasis T.degree (projection T)
    (projection_degree T) (projection_square T) p).map
      (LinearEquiv.ofEq _ _ (by rw [cast_projection T]))

#print axioms total_tf
#print axioms contraction
#print axioms pure_weight_int
#print axioms contraction_square
#print axioms contraction_generalized
#print axioms contraction_regular
#print axioms contraction_degree
#print axioms contraction_weight
#print axioms projection
#print axioms projection_square
#print axioms projection_degree
#print axioms retractionData
#print axioms integerDifferential
#print axioms residual_hA
#print axioms integer_square
#print axioms integer_degree
#print axioms integer_support
#print axioms integerComplex
#print axioms integerBasis
#print axioms equivalence
#print axioms cast_projection
#print axioms targetBasis

end Verification.TFEvenReduction

-- Explicit dependency audit of the early module constructions.
#print axioms Verification.TFEvenReduction.Input
