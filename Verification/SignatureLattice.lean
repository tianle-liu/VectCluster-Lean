/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Interval
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Lean.Elab.Tactic.Omega

/-!
# Signature Lattice

The finite integral algebra of the Boolean signature lattice in
manuscript.tex, Lemma `lem:lattice` (lines 3020–3051).

Subsets encode points of the Boolean cube by their sets of negative coordinates.
The monomial indexed by `A` has value one exactly on supersets of `A`.
We prove that its integer evaluation matrix has determinant one, and construct
the resulting lattice as an actual submodule of integer-valued functions.
No identification with Witt sheaves or a geometric signature map is assumed.
-/

namespace Verification.SignatureLattice

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Evaluation of the Boolean monomial indexed by `A` at the cube point `S`. -/
def booleanMonomial (A S : Finset α) : ℤ := if A ⊆ S then 1 else 0

/-- Rows are cube points; columns are Boolean monomials. -/
def evaluationMatrix : Matrix (Finset α) (Finset α) ℤ :=
  fun S A => booleanMonomial A S

omit [Fintype α] in
/-- Sorting subsets by cardinality makes the transpose block upper triangular. -/
theorem evaluation_transpose_blockTriangular :
    (evaluationMatrix (α := α)).transpose.BlockTriangular Finset.card := by
  intro A S h
  change (if A ⊆ S then (1 : ℤ) else 0) = 0
  exact if_neg (fun hAS => (Nat.not_le_of_lt h) (Finset.card_le_card hAS))

omit [Fintype α] in
/-- Every diagonal cardinality block of the evaluation transpose is an identity. -/
theorem evaluation_cardinality_block (k : ℕ) :
    ((evaluationMatrix (α := α)).transpose.toSquareBlock Finset.card k) = 1 := by
  ext A S
  simp only [Matrix.toSquareBlock_def, Matrix.transpose_apply, evaluationMatrix,
    booleanMonomial, Matrix.one_apply]
  by_cases h : A = S
  · subst S
    simp
  · have hAS : ¬ (A.val ⊆ S.val) := by
      intro hsub
      apply h
      apply Subtype.ext
      exact Finset.eq_of_subset_of_card_le hsub (by omega)
    simp [h, hAS]

/-- Boolean monomials form a unimodular evaluation matrix over the integers. -/
theorem evaluation_determinant : (evaluationMatrix (α := α)).det = 1 := by
  rw [← Matrix.det_transpose, evaluation_transpose_blockTriangular.det]
  simp [evaluation_cardinality_block]

/-- Evaluating an integer linear combination of Boolean monomials. -/
def evaluate : (Finset α → ℤ) →ₗ[ℤ] (Finset α → ℤ) :=
  (evaluationMatrix (α := α)).mulVecLin

theorem evaluate_apply (c : Finset α → ℤ) (S : Finset α) :
    evaluate c S = ∑ A : Finset α, booleanMonomial A S * c A := rfl

theorem evaluate_surjective : Function.Surjective (evaluate (α := α)) := by
  apply Matrix.mulVec_surjective_iff_isUnit.mpr
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [evaluation_determinant]
  exact isUnit_one

theorem evaluate_injective : Function.Injective (evaluate (α := α)) := by
  apply Matrix.mulVec_injective_of_isUnit
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [evaluation_determinant]
  exact isUnit_one

theorem evaluate_subset_sum (c : Finset α → ℤ) (S : Finset α) :
    evaluate c S = ∑ A ∈ Finset.Iic S, c A := by
  rw [evaluate_apply]
  simp only [booleanMonomial, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  congr 1
  ext A
  simp

/-- Integral Möbius inversion on the Boolean subset order. -/
noncomputable def mobiusCoefficients (f : Finset α → ℤ) (A : Finset α) : ℤ :=
  ∑ S ∈ Finset.Iic A, IncidenceAlgebra.mu ℤ S A * f S

theorem mobius_evaluate (c : Finset α → ℤ) (A : Finset α) :
    mobiusCoefficients (evaluate c) A = c A := by
  exact (IncidenceAlgebra.moebius_inversion_bot c (evaluate c)
    (evaluate_subset_sum c) A).symm

theorem evaluate_mobius (f : Finset α → ℤ) :
    evaluate (mobiusCoefficients f) = f := by
  obtain ⟨c, rfl⟩ := evaluate_surjective f
  congr 1
  funext A
  exact mobius_evaluate c A

/-- The evaluation transform is an integer linear equivalence. -/
noncomputable def evaluationEquiv : (Finset α → ℤ) ≃ₗ[ℤ] (Finset α → ℤ) :=
  LinearEquiv.ofBijective evaluate ⟨evaluate_injective, evaluate_surjective⟩

/-- `toNat` expresses `max (|A| - s) 0`, including negative integers `s`. -/
def exponent (s : ℤ) (A : Finset α) : ℕ := ((A.card : ℤ) - s).toNat

def boundExponent (s : ℤ) : ℕ := ((Fintype.card α : ℤ) - s).toNat

/-- The diagonal coefficient lattice before evaluating the Boolean monomials. -/
def coefficientLattice (s : ℤ) : Submodule ℤ (Finset α → ℤ) where
  carrier := {c | ∀ A, (2 : ℤ) ^ exponent s A ∣ c A}
  zero_mem' := fun _ => dvd_zero _
  add_mem' := fun hc hd A => dvd_add (hc A) (hd A)
  smul_mem' := fun r _ hc A => dvd_mul_of_dvd_right (hc A) r

/-- The actual lattice of integer-valued functions in the manuscript's formula. -/
def signatureLattice (s : ℤ) : Submodule ℤ (Finset α → ℤ) :=
  (coefficientLattice s).map evaluate

omit [DecidableEq α] in
theorem exponent_le_bound (s : ℤ) (A : Finset α) :
    exponent s A ≤ boundExponent (α := α) s := by
  apply Int.toNat_le_toNat
  have h := Finset.card_le_univ A
  omega

/-- Membership is exactly the divisibility of the unique monomial coefficients. -/
theorem mem_signatureLattice_iff (s : ℤ) (f : Finset α → ℤ) :
    f ∈ signatureLattice s ↔
      ∀ A, (2 : ℤ) ^ exponent s A ∣ mobiusCoefficients f A := by
  constructor
  · rintro ⟨c, hc, rfl⟩ A
    rw [mobius_evaluate]
    exact hc A
  · intro h
    exact ⟨mobiusCoefficients f, h, evaluate_mobius f⟩

/-- Multiplying any integer-valued function by the uniform bound puts it in Λ_s. -/
theorem scaled_function_mem (s : ℤ) (f : Finset α → ℤ) :
    ((2 : ℤ) ^ boundExponent (α := α) s) • f ∈ signatureLattice s := by
  obtain ⟨c, hc⟩ := evaluate_surjective f
  refine ⟨((2 : ℤ) ^ boundExponent (α := α) s) • c, ?_, ?_⟩
  · intro A
    exact dvd_mul_of_dvd_left (pow_dvd_pow (2 : ℤ) (exponent_le_bound s A)) (c A)
  · rw [map_smul, hc]

/-- The manuscript's scaled full function lattice as an actual submodule. -/
def scaledFunctionLattice (s : ℤ) : Submodule ℤ (Finset α → ℤ) :=
  LinearMap.range (((2 : ℤ) ^ boundExponent (α := α) s) • LinearMap.id)

theorem scaledFunctionLattice_le (s : ℤ) :
    scaledFunctionLattice (α := α) s ≤ signatureLattice s := by
  rintro f ⟨g, rfl⟩
  exact scaled_function_mem s g

/-- Arithmetic of the coefficient produced by normalized Pfister signatures. -/
theorem normalized_exponent (a : ℕ) (s : ℤ) :
    (a : ℤ) + max (s - a) 0 - s = max ((a : ℤ) - s) 0 := by omega

/-- In particular the image lattice is all integer-valued functions for `s ≥ t`. -/
theorem signatureLattice_eq_top (s : ℤ) (hs : (Fintype.card α : ℤ) ≤ s) :
    signatureLattice (α := α) s = ⊤ := by
  apply top_unique
  intro f _
  have hzero : boundExponent (α := α) s = 0 := by
    dsimp [boundExponent]
    omega
  simpa [hzero] using scaled_function_mem s f

#print axioms evaluation_transpose_blockTriangular
#print axioms evaluation_cardinality_block
#print axioms evaluation_determinant
#print axioms evaluate_apply
#print axioms evaluate_surjective
#print axioms evaluate_injective
#print axioms evaluate_subset_sum
#print axioms mobius_evaluate
#print axioms evaluate_mobius
#print axioms exponent_le_bound
#print axioms mem_signatureLattice_iff
#print axioms scaled_function_mem
#print axioms scaledFunctionLattice_le
#print axioms normalized_exponent
#print axioms signatureLattice_eq_top

end Verification.SignatureLattice

-- Explicit dependency audit of the early module constructions.
#print axioms Verification.SignatureLattice.booleanMonomial
#print axioms Verification.SignatureLattice.boundExponent
#print axioms Verification.SignatureLattice.coefficientLattice
#print axioms Verification.SignatureLattice.evaluate
#print axioms Verification.SignatureLattice.evaluationEquiv
#print axioms Verification.SignatureLattice.evaluationMatrix
#print axioms Verification.SignatureLattice.exponent
#print axioms Verification.SignatureLattice.mobiusCoefficients
#print axioms Verification.SignatureLattice.scaledFunctionLattice
#print axioms Verification.SignatureLattice.signatureLattice
