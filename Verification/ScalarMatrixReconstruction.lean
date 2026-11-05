/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarLaurentNormalForm

/-!
# Scalar Matrix Reconstruction

Every normalized finite Laurent exchange presentation is an ordinary
scalar matrix presentation, with the frozen column read in the chosen
basis. Thus the target class is the source class for another freezing.
-/
noncomputable section
namespace Verification.ScalarMatrixReconstruction
open Verification.ScalarLaurentNormalForm
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (P : Fin n → Fin n → ℤ) (f : Fin n → κ →₀ ℤ) (c : Fin n → Rˣ)

def matrix : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ :=
  fun r => Sum.elim (fun i => Sum.elim (fun j => P j i) (fun k => f i k) r) Empty.elim

omit [Fintype κ] in
theorem principal_matrix : principal κ n (matrix κ n P f) = P := rfl

theorem frozenColumn_matrix : frozenColumn κ n (matrix κ n P f) = f := by
  classical
  funext i
  ext k
  simp [frozenColumn, ExchangeCharacters.column, matrix, Finsupp.single_apply]

theorem ratio_one : ratio R n c (fun _ => 1) = c := by
  funext i
  simp [ratio]

def modelEquiv : LaurentScalarModel.Presentation R P f c ≃ₐ[R]
    ScalarFrozenGlobal.Global R κ n (matrix κ n P f) c (fun _ => 1) := by
  have e := globalEquiv R κ n (matrix κ n P f) c (fun _ => 1)
  rw [principal_matrix, frozenColumn_matrix, ratio_one] at e
  exact e.symm

#print axioms matrix
#print axioms principal_matrix
#print axioms frozenColumn_matrix
#print axioms ratio_one
#print axioms modelEquiv
end Verification.ScalarMatrixReconstruction
