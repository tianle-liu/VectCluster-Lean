/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

/-!
# Clique

The coefficient-row argument of manuscript.tex, lines 2220–2233.

The type `ι` indexes the selected columns, and `κ` indexes coefficient
cliques. Injectivity of `c : ι → κ` says that the selected columns have
distinct clique colors. We construct an actual linear left inverse for
the coefficient matrix, and for any matrix obtained by adding other rows.
Taking `R = ℤ` gives the split injection of lattices used in the paper.
This file does not formalize cluster varieties or the geometric (AS) condition.
-/

namespace Verification.Clique

variable {R ι κ μ : Type*} [CommRing R] [Fintype ι] [DecidableEq κ]

/-- The coefficient matrix, restricted to any chosen collection of columns. -/
def coefficientMatrix (c : ι → κ) : Matrix κ ι R :=
  fun a i => if c i = a then 1 else 0

/-- Reading the coefficient row carrying the color of each selected column. -/
def rowRetraction (c : ι → κ) : (κ → R) →ₗ[R] (ι → R) where
  toFun y i := y (c i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype ι] in
/-- The selected coefficient rows form an identity submatrix. -/
theorem coefficient_rows_identity [DecidableEq ι] (c : ι → κ) (hc : Function.Injective c)
    (i j : ι) :
    coefficientMatrix (R := R) c (c i) j = if j = i then 1 else 0 := by
  classical
  simp only [coefficientMatrix, hc.eq_iff]

/-- The row-reading linear map is a left inverse to the coefficient matrix. -/
theorem coefficient_left_inverse (c : ι → κ) (hc : Function.Injective c) :
    Function.LeftInverse (rowRetraction (R := R) c)
      (coefficientMatrix (R := R) c).mulVecLin := by
  classical
  intro x
  funext i
  simp [rowRetraction, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    coefficientMatrix, hc.eq_iff, ite_mul]

/-- The same splitting expressed as equality of linear maps. -/
theorem coefficient_split (c : ι → κ) (hc : Function.Injective c) :
    (rowRetraction (R := R) c).comp (coefficientMatrix (R := R) c).mulVecLin =
      LinearMap.id := by
  ext x i
  exact congrFun (coefficient_left_inverse (R := R) c hc x) i

theorem coefficient_injective (c : ι → κ) (hc : Function.Injective c) :
    Function.Injective (coefficientMatrix (R := R) c).mulVecLin :=
  (coefficient_left_inverse (R := R) c hc).injective

/-- Additional rows are arbitrary; the coefficient block remains unchanged. -/
def extendedMatrix (B : Matrix μ ι R) (c : ι → κ) : Matrix (μ ⊕ κ) ι R :=
  fun a i => Sum.elim (fun b => B b i) (fun b => coefficientMatrix c b i) a

/-- Reading coefficient rows also retracts the full extended matrix. -/
def extendedRetraction (c : ι → κ) : ((μ ⊕ κ) → R) →ₗ[R] (ι → R) where
  toFun y i := y (Sum.inr (c i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem extended_left_inverse (B : Matrix μ ι R) (c : ι → κ)
    (hc : Function.Injective c) :
    Function.LeftInverse (extendedRetraction (R := R) (μ := μ) c)
      (extendedMatrix B c).mulVecLin := by
  classical
  intro x
  funext i
  simp [extendedRetraction, extendedMatrix, Matrix.mulVecLin_apply,
    Matrix.mulVec, dotProduct, coefficientMatrix, hc.eq_iff, ite_mul]

theorem extended_split (B : Matrix μ ι R) (c : ι → κ)
    (hc : Function.Injective c) :
    (extendedRetraction (R := R) (μ := μ) c).comp (extendedMatrix B c).mulVecLin =
      LinearMap.id := by
  ext x i
  exact congrFun (extended_left_inverse B c hc x) i

theorem extended_injective (B : Matrix μ ι R) (c : ι → κ)
    (hc : Function.Injective c) : Function.Injective (extendedMatrix B c).mulVecLin :=
  (extended_left_inverse B c hc).injective

#print axioms coefficient_rows_identity
#print axioms coefficient_left_inverse
#print axioms coefficient_split
#print axioms coefficient_injective
#print axioms extended_left_inverse
#print axioms extended_split
#print axioms extended_injective

end Verification.Clique

-- Explicit dependency audit of the early module constructions.
#print axioms Verification.Clique.coefficientMatrix
#print axioms Verification.Clique.extendedMatrix
#print axioms Verification.Clique.extendedRetraction
#print axioms Verification.Clique.rowRetraction
