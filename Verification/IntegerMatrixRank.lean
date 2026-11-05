/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

/-!
# Integer Matrix Rank

Ranks of finite integer matrices are unchanged by rationalization
and transposition. These are ranks of the actual images, including when
the integer image is not saturated.
-/
noncomputable section
namespace Verification.IntegerMatrixRank
open scoped nonZeroDivisors
variable {ι κ : Type} [Fintype ι] [Fintype κ]

def rationalCoordinates : (ι → ℤ) →ₗ[ℤ] (ι → ℚ) :=
  LinearMap.pi (fun i => (Algebra.linearMap ℤ ℚ).comp (LinearMap.proj i))

theorem rationalization (a : Matrix ι κ ℤ) : (a.map (Int.castRingHom ℚ)).rank=a.rank := by
  let f : (ι → ℤ) →ₗ[ℤ] (ι → ℚ) := rationalCoordinates
  letI : IsLocalizedModule ℤ⁰ f :=
    IsLocalizedModule.pi ℤ⁰ (fun _ : ι => Algebra.linearMap ℤ ℚ)
  let U := Submodule.span ℤ (Set.range a.col)
  have hr := IsLocalizedModule.finrank_eq ℤ⁰ (U.toLocalized' ℚ ℤ⁰ f) le_rfl
  have hs := IsLocalization.rank_eq ℚ ℤ⁰ (N := U.localized' ℚ ℤ⁰ f) le_rfl
  have hs' := congrArg Cardinal.toNat hs
  change Module.finrank ℚ (U.localized' ℚ ℤ⁰ f)=Module.finrank ℤ (U.localized' ℚ ℤ⁰ f) at hs'
  have he : U.localized' ℚ ℤ⁰ f=Submodule.span ℚ (Set.range (a.map (Int.castRingHom ℚ)).col) := by
    dsimp only [U]
    rw [Submodule.localized'_span]
    congr 1
    rw [← Set.range_comp]
    rfl
  have h := hs'.trans hr
  rw [he] at h
  rw [Matrix.rank_eq_finrank_span_cols,Matrix.rank_eq_finrank_span_cols]
  exact h

theorem transpose (a : Matrix ι κ ℤ) : a.transpose.rank=a.rank := by
  rw [← rationalization a.transpose,← rationalization a]
  exact Matrix.rank_transpose (a.map (Int.castRingHom ℚ))

#print axioms rationalCoordinates
#print axioms rationalization
#print axioms transpose
end Verification.IntegerMatrixRank
