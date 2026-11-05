/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathWeightBasis

/-!
# Path Sign Normalization

Literal g-dependent first-boundary columns and the manuscript's positional
sign change. This establishes the normalization before any specialization of g.
-/

namespace Verification.PathSignNormalization

open Classical Verification.Path Verification.PathWords Verification.PathFirstBoundary
  Verification.PathCokernel Verification.PathWeightBasis

/-- Sum of the actual selected positions, starting at a specified offset. -/
def indexSum : ℕ → List Bool → ℕ
  | _, [] => 0
  | i, b::tail => (if b then i else 0)+indexSum (i+1) tail

theorem indexSum_append (pre post : List Bool) (i : ℕ) :
    indexSum i (pre++post)=indexSum i pre+indexSum (i+pre.length) post := by
  induction pre generalizing i with
  | nil => simp [indexSum]
  | cons b tail ih =>
    simp only [List.cons_append, indexSum, ih, List.length_cons]
    simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Every original local slide raises the positional sum by exactly two. -/
theorem indexSum_slide (pre post : List Bool) (i : ℕ) :
    indexSum i (pre++false::true::true::post)=
      indexSum i (pre++true::true::false::post)+2 := by
  simp only [indexSum_append, indexSum, Bool.false_eq_true, ↓reduceIte]
  omega

variable {R : Type*} [CommRing R]

/-- A general involutive diagonal change of a free module. -/
noncomputable def diagonal {ι : Type*} (s : ι → R) : (ι →₀ R) →ₗ[R] (ι →₀ R) :=
  Finsupp.linearCombination R (fun i => s i • Finsupp.single i 1)

theorem diagonal_single {ι : Type*} (s : ι → R) (i : ι) :
    diagonal s (Finsupp.single i 1)=s i • Finsupp.single i 1 := by
  simp only [diagonal, Finsupp.linearCombination_single, one_smul]

theorem diagonal_squared {ι : Type*} (s : ι → R) (hs : ∀ i, s i*s i=1) :
    (diagonal s).comp (diagonal s)=LinearMap.id := by
  apply Finsupp.lhom_ext
  intro i r
  have hr : Finsupp.single i r=r • Finsupp.single i (1 : R) := by simp
  rw [hr, map_smul, map_smul]
  congr 1
  simp only [LinearMap.comp_apply, diagonal_single, map_smul, smul_smul, hs,
    one_smul, LinearMap.id_apply]

noncomputable def diagonalEquiv {ι : Type*} (s : ι → R) (hs : ∀ i, s i*s i=1) :
    (ι →₀ R) ≃ₗ[R] (ι →₀ R) :=
  LinearEquiv.ofLinear (diagonal s) (diagonal s) (diagonal_squared s hs) (diagonal_squared s hs)

variable (g : R) (hg : g*g=1) (m : Bool) (n : ℕ)

/-- The exact exponent from the manuscript, evaluated on original words. -/
def wordScale (w : Word n) : R := g^(indexSum 0 w.val/2)

include hg in
theorem wordScale_squared (w : Word n) : wordScale g n w*wordScale g n w=1 := by
  simp only [wordScale, ← mul_pow, hg, one_pow]

noncomputable def wordEquiv : (Word n →₀ R) ≃ₗ[R] (Word n →₀ R) :=
  diagonalEquiv (wordScale g n) (wordScale_squared g hg n)

def sourceScale : BoundaryIndex m n → R
  | Sum.inl w => wordScale g n w.val
  | Sum.inr uv => wordScale g n uv.val.1

include hg in
theorem sourceScale_squared (j : BoundaryIndex m n) : sourceScale g m n j*sourceScale g m n j=1 := by
  cases j with
  | inl w => exact wordScale_squared g hg n w.val
  | inr uv => exact wordScale_squared g hg n uv.val.1

noncomputable def sourceEquiv : (BoundaryIndex m n →₀ R) ≃ₗ[R] (BoundaryIndex m n →₀ R) :=
  diagonalEquiv (sourceScale g m n) (sourceScale_squared g hg m n)

/-- All original unit relations with the unspecialized slide coefficient g. -/
noncomputable def signedColumn : BoundaryIndex m n → (Word n →₀ R)
  | Sum.inl w => Finsupp.single w.val 1
  | Sum.inr uv => Finsupp.single uv.val.1 1-g • Finsupp.single uv.val.2 1

noncomputable def signedBoundary : (BoundaryIndex m n →₀ R) →ₗ[R] (Word n →₀ R) :=
  Finsupp.linearCombination R (signedColumn g m n)

include hg in
theorem slide_scale (u v : Word n) (h : Slide u v) : g*wordScale g n v=wordScale g n u := by
  obtain ⟨pre,post,h₁,h₂⟩ := h
  have hs := indexSum_slide pre post 0
  rw [← h₁, ← h₂] at hs
  simp only [wordScale, hs]
  rw [mul_comm]
  exact slide_basis_sign g hg _

theorem normalized_column (j : BoundaryIndex m n) :
    wordEquiv g hg n (signedColumn g m n j)=sourceScale g m n j • relationColumn m n j := by
  change diagonal (wordScale g n) _=_
  cases j with
  | inl w => exact diagonal_single _ _
  | inr uv =>
    simp only [signedColumn, map_sub, map_smul, diagonal_single, smul_smul,
      slide_scale g hg n _ _ uv.property, sourceScale, relationColumn, smul_sub]

/-- Literal intertwining of the two finite matrices, including every coefficient. -/
theorem boundary_intertwining :
    (wordEquiv g hg n).toLinearMap.comp (signedBoundary g m n)=
      (firstBoundary m n).comp (sourceEquiv g hg m n).toLinearMap := by
  apply Finsupp.lhom_ext
  intro j r
  have hr : Finsupp.single j r=r • Finsupp.single j (1 : R) := by simp
  rw [hr, map_smul, map_smul]
  congr 1
  change wordEquiv g hg n (signedBoundary g m n (Finsupp.single j 1))=_
  simp only [signedBoundary, Finsupp.linearCombination_single, one_smul]
  change wordEquiv g hg n (signedColumn g m n j)=firstBoundary m n (diagonal (sourceScale g m n) (Finsupp.single j 1))
  rw [diagonal_single, map_smul]
  simp only [firstBoundary, Finsupp.linearCombination_single, one_smul]
  exact normalized_column g hg m n j

#print axioms indexSum
#print axioms indexSum_append
#print axioms indexSum_slide
#print axioms diagonal
#print axioms diagonal_single
#print axioms diagonal_squared
#print axioms diagonalEquiv
#print axioms wordScale
#print axioms wordScale_squared
#print axioms wordEquiv
#print axioms sourceScale
#print axioms sourceScale_squared
#print axioms sourceEquiv
#print axioms signedColumn
#print axioms signedBoundary
#print axioms slide_scale
#print axioms normalized_column
#print axioms boundary_intertwining

end Verification.PathSignNormalization
