/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.LinearAlgebra.Prod
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

/-!
# Explicit two-term cancellation and finite weight filtrations

This file checks the algebraic cancellation used at manuscript.tex 1639--1678.
A differential `d : C₁ →ₗ[R] C₀` denotes the actual complex supported in
degrees one and zero. `TwoTermMap` and `TwoTermHomotopyEquiv` record its
linear chain maps and the two degreewise chain-homotopy equations.

The constructed homotopy equivalence cancels an invertible block of a
general differential `[[A,B],[C,D]]`, leaving `D - C A⁻¹ B`.
The finite matrix results derive nilpotence from strict weight increase;
nilpotence itself is not taken as a hypothesis.

These theorems do not construct the geometric cellular complex or identify
its matrices with the displayed algebraic blocks.
-/

namespace Verification.ChainCancellation

section TwoTerm

variable {R : Type*} [CommRing R]
variable {X₁ X₀ Y₁ Y₀ : Type*}
variable [AddCommGroup X₁] [AddCommGroup X₀] [AddCommGroup Y₁] [AddCommGroup Y₀]
variable [Module R X₁] [Module R X₀] [Module R Y₁] [Module R Y₀]

/-- A chain map between complexes concentrated in degrees one and zero. -/
structure TwoTermMap (dX : X₁ →ₗ[R] X₀) (dY : Y₁ →ₗ[R] Y₀) where
  degreeOne : X₁ →ₗ[R] Y₁
  degreeZero : X₀ →ₗ[R] Y₀
  commutes : degreeZero.comp dX = dY.comp degreeOne

/-- Explicit chain maps and homotopies for two-term chain complexes. -/
structure TwoTermHomotopyEquiv (dX : X₁ →ₗ[R] X₀) (dY : Y₁ →ₗ[R] Y₀) where
  forward : TwoTermMap dX dY
  backward : TwoTermMap dY dX
  homotopyX : X₀ →ₗ[R] X₁
  homotopyY : Y₀ →ₗ[R] Y₁
  identityXOne : LinearMap.id - backward.degreeOne.comp forward.degreeOne = homotopyX.comp dX
  identityXZero : LinearMap.id - backward.degreeZero.comp forward.degreeZero = dX.comp homotopyX
  identityYOne : LinearMap.id - forward.degreeOne.comp backward.degreeOne = homotopyY.comp dY
  identityYZero : LinearMap.id - forward.degreeZero.comp backward.degreeZero = dY.comp homotopyY

variable {M N U V : Type*}
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup U] [AddCommGroup V]
variable [Module R M] [Module R N] [Module R U] [Module R V]

/-- The full two-by-two block differential. -/
def blockDifferential (A : M ≃ₗ[R] N) (B : U →ₗ[R] N)
    (C : M →ₗ[R] V) (D : U →ₗ[R] V) : M × U →ₗ[R] N × V :=
  ((A.toLinearMap.comp (LinearMap.fst R M U)) + B.comp (LinearMap.snd R M U)).prod
    (C.comp (LinearMap.fst R M U) + D.comp (LinearMap.snd R M U))

/-- The residual differential after cancelling the invertible block. -/
def schurComplement (A : M ≃ₗ[R] N) (B : U →ₗ[R] N)
    (C : M →ₗ[R] V) (D : U →ₗ[R] V) : U →ₗ[R] V :=
  D - C.comp (A.symm.toLinearMap.comp B)

def cancelProjectionZero (A : M ≃ₗ[R] N) (C : M →ₗ[R] V) : N × V →ₗ[R] V :=
  LinearMap.snd R N V - C.comp (A.symm.toLinearMap.comp (LinearMap.fst R N V))

def cancelInclusionOne (A : M ≃ₗ[R] N) (B : U →ₗ[R] N) : U →ₗ[R] M × U :=
  (-(A.symm.toLinearMap.comp B)).prod LinearMap.id

def cancelHomotopy (A : M ≃ₗ[R] N) : N × V →ₗ[R] M × U :=
  (A.symm.toLinearMap.comp (LinearMap.fst R N V)).prod 0

theorem cancel_projection_chain (A : M ≃ₗ[R] N) (B : U →ₗ[R] N)
    (C : M →ₗ[R] V) (D : U →ₗ[R] V) :
    (cancelProjectionZero A C).comp (blockDifferential A B C D) =
      (schurComplement A B C D).comp (LinearMap.snd R M U) := by
  ext x <;> simp [cancelProjectionZero, blockDifferential, schurComplement]

theorem cancel_inclusion_chain (A : M ≃ₗ[R] N) (B : U →ₗ[R] N)
    (C : M →ₗ[R] V) (D : U →ₗ[R] V) :
    (blockDifferential A B C D).comp (cancelInclusionOne A B) =
      (LinearMap.inr R N V).comp (schurComplement A B C D) := by
  ext u <;> simp [blockDifferential, cancelInclusionOne, schurComplement]
  abel

theorem cancel_homotopy_degree_one (A : M ≃ₗ[R] N) (B : U →ₗ[R] N)
    (C : M →ₗ[R] V) (D : U →ₗ[R] V) :
    LinearMap.id - (cancelInclusionOne A B).comp (LinearMap.snd R M U) =
      (cancelHomotopy A).comp (blockDifferential A B C D) := by
  ext x <;> simp [cancelInclusionOne, cancelHomotopy, blockDifferential]

theorem cancel_homotopy_degree_zero (A : M ≃ₗ[R] N) (B : U →ₗ[R] N)
    (C : M →ₗ[R] V) (D : U →ₗ[R] V) :
    LinearMap.id - (LinearMap.inr R N V).comp (cancelProjectionZero A C) =
      (blockDifferential A B C D).comp (cancelHomotopy A) := by
  ext x <;> simp [cancelProjectionZero, cancelHomotopy, blockDifferential]

/-- The complete chain-homotopy equivalence, with every map constructed. -/
def blockCancellation (A : M ≃ₗ[R] N) (B : U →ₗ[R] N)
    (C : M →ₗ[R] V) (D : U →ₗ[R] V) :
    TwoTermHomotopyEquiv (blockDifferential A B C D) (schurComplement A B C D) where
  forward := {
    degreeOne := LinearMap.snd R M U
    degreeZero := cancelProjectionZero A C
    commutes := cancel_projection_chain A B C D }
  backward := {
    degreeOne := cancelInclusionOne A B
    degreeZero := LinearMap.inr R N V
    commutes := (cancel_inclusion_chain A B C D).symm }
  homotopyX := cancelHomotopy A
  homotopyY := 0
  identityXOne := cancel_homotopy_degree_one A B C D
  identityXZero := cancel_homotopy_degree_zero A B C D
  identityYOne := by ext u; simp [cancelInclusionOne]
  identityYZero := by ext v; simp [cancelProjectionZero]

/-- A concrete zero module, used for the complex concentrated in degree zero. -/
abbrev ZeroSource (R : Type*) := Fin 0 → R

/-- If every source belongs to the pivot block, only the degree-zero target survives. -/
def completeSourceCancellation (A : M ≃ₗ[R] N) (C : M →ₗ[R] V) :
    TwoTermHomotopyEquiv (A.toLinearMap.prod C) (0 : ZeroSource R →ₗ[R] V) where
  forward := {
    degreeOne := 0
    degreeZero := cancelProjectionZero A C
    commutes := by ext x; simp [cancelProjectionZero] }
  backward := {
    degreeOne := 0
    degreeZero := LinearMap.inr R N V
    commutes := by simp }
  homotopyX := A.symm.toLinearMap.comp (LinearMap.fst R N V)
  homotopyY := 0
  identityXOne := by ext x; simp
  identityXZero := by ext x <;> simp [cancelProjectionZero]
  identityYOne := by ext f i; exact Fin.elim0 i
  identityYZero := by ext v; simp [cancelProjectionZero]

end TwoTerm

section FiniteWeights

variable {R : Type*} [Ring R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A `k`-fold product raises weight by at least `k`. -/
theorem raising_matrix_power (N : Matrix ι ι R) (w : ι → ℕ)
    (hN : ∀ i j, w i ≤ w j → N i j = 0) (k : ℕ) :
    ∀ i j, w i < w j + k → (N ^ k) i j = 0 := by
  induction k with
  | zero =>
      intro i j hij
      have hne : i ≠ j := by intro he; subst j; omega
      simp [hne]
  | succ k ih =>
      intro i j hij
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro z _
      by_cases hz : w z ≤ w j
      · rw [hN z j hz, mul_zero]
      · rw [ih i z (by omega), zero_mul]

/-- Bounded weights give the concrete nilpotence exponent `bound + 1`. -/
theorem raising_matrix_nilpotent (N : Matrix ι ι R) (w : ι → ℕ) (bound : ℕ)
    (hw : ∀ i, w i ≤ bound) (hN : ∀ i j, w i ≤ w j → N i j = 0) :
    N ^ (bound + 1) = 0 := by
  ext i j
  exact raising_matrix_power N w hN (bound + 1) i j (by have := hw i; omega)

/-- The finite inverse conclusion now has no assumed nilpotence hypothesis. -/
theorem one_add_raising_matrix_isUnit (N : Matrix ι ι R) (w : ι → ℕ) (bound : ℕ)
    (hw : ∀ i, w i ≤ bound) (hN : ∀ i j, w i ≤ w j → N i j = 0) :
    IsUnit (1 + N) :=
  IsNilpotent.isUnit_one_add ⟨bound + 1, raising_matrix_nilpotent N w bound hw hN⟩

/-- The inverse of a weight-preserving invertible matrix preserves the same weights. -/
theorem weight_preserving_inverse (A : (Matrix ι ι R)ˣ) (w : ι → ℕ)
    (hA : ∀ i j, w i ≠ w j → A.val i j = 0) :
    ∀ i j, w i ≠ w j → A.inv i j = 0 := by
  intro i j hij
  let P : Matrix ι ι R := Matrix.diagonal (fun z => if w z = w i then 1 else 0)
  have hc : Commute P A.val := by
    change P * A.val = A.val * P
    ext a b
    simp only [P, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hab : w a = w b
    · rw [hab]
      by_cases hb : w b = w i <;> simp [hb]
    · rw [hA a b hab]
      simp
  have hinv : Commute P A.inv := hc.units_inv_right
  have he := congrArg (fun T : Matrix ι ι R => T i j) hinv.eq
  simpa only [P, Matrix.diagonal_mul, Matrix.mul_diagonal, eq_self_iff_true, ite_true,
    if_neg (Ne.symm hij), one_mul, mul_zero] using he

/-- Multiplying by the inverse of a weight-preserving pivot retains strict increase. -/
theorem inverse_pivot_mul_raises (A : (Matrix ι ι R)ˣ) (E : Matrix ι ι R) (w : ι → ℕ)
    (hA : ∀ i j, w i ≠ w j → A.inv i j = 0)
    (hE : ∀ i j, w i ≤ w j → E i j = 0) :
    ∀ i j, w i ≤ w j → (A.inv * E) i j = 0 := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro z _
  by_cases hz : w i = w z
  · rw [hE z j (by omega), mul_zero]
  · rw [hA i z hz, zero_mul]

/-- An invertible pivot plus a strictly weight-raising error is invertible. -/
theorem pivot_add_raising_isUnit (A : (Matrix ι ι R)ˣ) (E : Matrix ι ι R)
    (w : ι → ℕ) (bound : ℕ) (hw : ∀ i, w i ≤ bound)
    (hA : ∀ i j, w i ≠ w j → A.val i j = 0)
    (hE : ∀ i j, w i ≤ w j → E i j = 0) :
    IsUnit (A.val + E) := by
  have hu := one_add_raising_matrix_isUnit (A.inv * E)
    w bound hw (inverse_pivot_mul_raises A E w (weight_preserving_inverse A w hA) hE)
  have hAunit : IsUnit A.val := ⟨A, rfl⟩
  have hp : IsUnit (A.val * (1 + A.inv * E)) := hAunit.mul hu
  have he : A.val * (1 + A.inv * E) = A.val + E := by
    rw [mul_add, mul_one, ← mul_assoc, A.val_inv, one_mul]
  exact he ▸ hp

end FiniteWeights

section MatrixRealization

variable {R : Type*} [CommRing R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Realize a matrix unit as the actual linear equivalence on coordinate vectors. -/
def unitMatrixEquiv (A : (Matrix ι ι R)ˣ) : (ι → R) ≃ₗ[R] (ι → R) :=
  Matrix.toLin'OfInv A.inv_val A.val_inv

theorem unitMatrixEquiv_apply (A : (Matrix ι ι R)ˣ) (x : ι → R) :
    unitMatrixEquiv A x = Matrix.mulVec A.val x := rfl

/-- The finite-weight construction supplies the linear equivalence needed by cancellation. -/
theorem weighted_pivot_linear_equiv (A : (Matrix ι ι R)ˣ) (E : Matrix ι ι R)
    (w : ι → ℕ) (bound : ℕ) (hw : ∀ i, w i ≤ bound)
    (hA : ∀ i j, w i ≠ w j → A.val i j = 0)
    (hE : ∀ i j, w i ≤ w j → E i j = 0) :
    ∃ Q : (ι → R) ≃ₗ[R] (ι → R), ∀ x, Q x = Matrix.mulVec (A.val + E) x := by
  obtain ⟨Q, hQ⟩ := pivot_add_raising_isUnit A E w bound hw hA hE
  refine ⟨unitMatrixEquiv Q, ?_⟩
  intro x
  change Matrix.mulVec Q.val x = Matrix.mulVec (A.val + E) x
  rw [hQ]

end MatrixRealization

#print axioms cancel_projection_chain
#print axioms cancel_inclusion_chain
#print axioms cancel_homotopy_degree_one
#print axioms cancel_homotopy_degree_zero
#print axioms blockCancellation
#print axioms completeSourceCancellation
#print axioms raising_matrix_power
#print axioms raising_matrix_nilpotent
#print axioms one_add_raising_matrix_isUnit
#print axioms weight_preserving_inverse
#print axioms inverse_pivot_mul_raises
#print axioms pivot_add_raising_isUnit
#print axioms unitMatrixEquiv_apply
#print axioms weighted_pivot_linear_equiv

end Verification.ChainCancellation

-- Explicit dependency audit of the early module constructions.
#print axioms Verification.ChainCancellation.TwoTermHomotopyEquiv
#print axioms Verification.ChainCancellation.TwoTermMap
#print axioms Verification.ChainCancellation.ZeroSource
#print axioms Verification.ChainCancellation.blockDifferential
#print axioms Verification.ChainCancellation.cancelHomotopy
#print axioms Verification.ChainCancellation.cancelInclusionOne
#print axioms Verification.ChainCancellation.cancelProjectionZero
#print axioms Verification.ChainCancellation.schurComplement
#print axioms Verification.ChainCancellation.unitMatrixEquiv
