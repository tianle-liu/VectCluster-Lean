/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Algebra.GeomSum
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Algebra

Algebraic steps in manuscript.tex, lines 1659–1663, 1711–1725,
and 2484–2488. These statements concern actual rings and matrices.
They do not assert that a geometric cellular differential has this form.
-/

namespace Verification.Algebra

open Finset Polynomial

/-- The finite inverse used in the path cancellation, valid in noncommutative rings. -/
theorem finite_inverse {R : Type*} [Ring R] (N : R) (m : ℕ) (hn : N ^ m = 0) :
    (∑ i ∈ range m, (-N) ^ i) * (1 + N) = 1 ∧
    (1 + N) * (∑ i ∈ range m, (-N) ^ i) = 1 := by
  have hneg : (-N) ^ m = 0 := by rw [neg_pow, hn, mul_zero]
  constructor
  · simpa [hneg] using geom_sum_mul_neg (-N) m
  · simpa [hneg] using mul_neg_geom_sum (-N) m

/-- This applies, in particular, to the square matrix block in the path proof. -/
theorem one_add_nilpotent_isUnit {R : Type*} [Ring R]
    (N : R) (m : ℕ) (hn : N ^ m = 0) : IsUnit (1 + N) := by
  obtain ⟨hl, hr⟩ := finite_inverse N m hn
  exact ⟨⟨1 + N, ∑ i ∈ range m, (-N) ^ i, hr, hl⟩, rfl⟩

/-- The common-monomial normalization, coordinate by coordinate for exponent vectors. -/
theorem normalize_exponents (a b : ℤ) :
    a - min a b = max (a - b) 0 ∧
    b - min a b = max (b - a) 0 := by omega

/-- Frozen substitution subtracts exactly the mutable-row contribution. -/
theorem frozen_exponent_difference (c u v : ℤ) :
    (max c 0 - u) - (max (-c) 0 - v) = c - (u - v) := by omega

/-- The scalar relation used in reducing every positive power of the hyperbolic form. -/
theorem hyperbolic_power {R : Type*} [CommRing R]
    (h : R) (hh : h ^ 2 = 2 * h) (n : ℕ) :
    h ^ (n + 1) = 2 ^ n * h := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      h ^ (n + 1 + 1) = (2 ^ n * h) * h := by rw [pow_succ, ih]
      _ = 2 ^ n * h ^ 2 := by ring
      _ = 2 ^ n * (2 * h) := by rw [hh]
      _ = 2 ^ (n + 1) * h := by rw [pow_succ]; ring

/-- The manuscript's ring R_h, as the literal polynomial quotient. -/
noncomputable def hyperbolicPolynomial : ℤ[X] := X ^ 2 - C 2 * X

abbrev HyperbolicRing := AdjoinRoot hyperbolicPolynomial

noncomputable def hyperbolic : HyperbolicRing := AdjoinRoot.root hyperbolicPolynomial

theorem hyperbolic_relation : hyperbolic ^ 2 = 2 * hyperbolic := by
  have hr := AdjoinRoot.eval₂_root hyperbolicPolynomial
  simpa [hyperbolicPolynomial, hyperbolic, sub_eq_zero] using hr

/-- Evaluation at h=2 detects an integer multiplied by 2h. -/
noncomputable def evaluateAtTwo : HyperbolicRing →+* ℤ :=
  AdjoinRoot.lift (RingHom.id ℤ) 2 (by norm_num [hyperbolicPolynomial])

theorem evaluate_hyperbolic : evaluateAtTwo hyperbolic = 2 := by
  exact AdjoinRoot.lift_root _

theorem integer_coefficient_detected (a : ℤ)
    (ha : 2 * hyperbolic * (a : HyperbolicRing) = 0) : a = 0 := by
  have he := congrArg evaluateAtTwo ha
  simp only [map_mul, map_ofNat, evaluate_hyperbolic, map_intCast, map_zero] at he
  norm_num at he
  exact he

/-- Matrix consequence in the even-reduction lemma: no cancellation of h is assumed. -/
theorem integer_matrix_square_zero {n : Type*} [Fintype n]
    (A : Matrix n n ℤ)
    (ha : ∀ i j, 2 * hyperbolic * (((A * A) i j : ℤ) : HyperbolicRing) = 0) :
    A * A = 0 := by
  ext i j
  exact integer_coefficient_detected ((A * A) i j) (ha i j)

/-- The literal differential hA from the even-reduction argument. -/
noncomputable def hyperbolicMatrix {n : Type*} (A : Matrix n n ℤ) :
    Matrix n n HyperbolicRing := fun i j => hyperbolic * (A i j : HyperbolicRing)

theorem hyperbolic_matrix_square {n : Type*} [Fintype n]
    (A : Matrix n n ℤ) (i j : n) :
    (hyperbolicMatrix A * hyperbolicMatrix A) i j =
      2 * hyperbolic * (((A * A) i j : ℤ) : HyperbolicRing) := by
  simp only [Matrix.mul_apply, hyperbolicMatrix, Int.cast_sum, Int.cast_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  calc
    (hyperbolic * (A i k : HyperbolicRing)) * (hyperbolic * (A k j : HyperbolicRing)) =
        hyperbolic ^ 2 * ((A i k : HyperbolicRing) * (A k j : HyperbolicRing)) := by ring
    _ = 2 * hyperbolic * ((A i k : HyperbolicRing) * (A k j : HyperbolicRing)) := by
      rw [hyperbolic_relation]

/-- Square-zero for the actual hA differential forces A itself to square to zero. -/
theorem hyperbolic_differential_detects_integer_complex {n : Type*} [Fintype n]
    (A : Matrix n n ℤ) (hd : hyperbolicMatrix A * hyperbolicMatrix A = 0) :
    A * A = 0 := by
  apply integer_matrix_square_zero
  intro i j
  rw [← hyperbolic_matrix_square, hd]
  rfl

#print axioms finite_inverse
#print axioms one_add_nilpotent_isUnit
#print axioms normalize_exponents
#print axioms frozen_exponent_difference
#print axioms hyperbolic_power
#print axioms hyperbolic_relation
#print axioms evaluate_hyperbolic
#print axioms integer_coefficient_detected
#print axioms integer_matrix_square_zero
#print axioms hyperbolic_matrix_square
#print axioms hyperbolic_differential_detects_integer_complex

end Verification.Algebra

-- Explicit dependency audit of the early module constructions.
#print axioms Verification.Algebra.HyperbolicRing
#print axioms Verification.Algebra.evaluateAtTwo
#print axioms Verification.Algebra.hyperbolic
#print axioms Verification.Algebra.hyperbolicMatrix
#print axioms Verification.Algebra.hyperbolicPolynomial
