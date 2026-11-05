/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GradedPerturbation

/-!
# Zero Weight Matrix Block

The unique weight-zero coordinate is a separate constant block. The
lemmas use cellular degree and the proved matrix weight support only.
-/

namespace Verification.ZeroWeightMatrixBlock

open Verification.GradedPerturbation

variable {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι]
variable (d : ι → ℤ) (w : ι → ℕ) (z : ι)

omit [Fintype ι] [DecidableEq ι] in
theorem differential_column (D : Matrix ι ι R) (hD : Homogeneous d 1 D)
    (hn : ∀i,d i≤0) (hz : d z=0) : ∀i,D i z=0 := by
  intro i
  exact hD i z (by have hi:=hn i;omega)

omit [Fintype ι] [DecidableEq ι] in
theorem differential_row (D : Matrix ι ι R) (hD : Homogeneous d 1 D)
    (hn : ∀i,d i≤0) (hz : d z=0) (hwz : w z=0) (hu : ∀i,w i=0 → i=z)
    (hwD : ∀i j,w i<w j → D i j=0) : ∀j,D z j=0 := by
  intro j
  by_cases hj : w j=0
  · rw [hu j hj]
    exact differential_column d z D hD hn hz z
  · exact hwD z j (by omega)

omit [Fintype ι] [DecidableEq ι] in
theorem homotopy_column (H : Matrix ι ι R) (hH : Homogeneous d (-1) H)
    (hwz : w z=0) (hu : ∀i,w i=0 → i=z) (hwH : ∀i j,w i≠w j → H i j=0) :
    ∀i,H i z=0 := by
  intro i
  by_cases hi : w i=0
  · rw [hu i hi]
    exact hH z z (by omega)
  · exact hwH i z (by omega)

omit [Fintype ι] [DecidableEq ι] in
theorem homotopy_row (H : Matrix ι ι R) (hH : Homogeneous d (-1) H)
    (hwz : w z=0) (hu : ∀i,w i=0 → i=z) (hwH : ∀i j,w i≠w j → H i j=0) :
    ∀j,H z j=0 := by
  intro j
  by_cases hj : w j=0
  · rw [hu j hj]
    exact hH z z (by omega)
  · exact hwH z j (by omega)

def constantProjection : Matrix ι ι R := Matrix.diagonal (fun i=>if i=z then 1 else 0)

theorem annihilate_left (M : Matrix ι ι R) (hm : ∀j,M z j=0) :
    constantProjection z*M=0 := by
  ext i j
  rw [constantProjection,Matrix.diagonal_mul]
  by_cases hi : i=z
  · subst i
    simp [hm]
  · simp [hi]

theorem annihilate_right (M : Matrix ι ι R) (hm : ∀i,M i z=0) :
    M*constantProjection z=0 := by
  ext i j
  rw [constantProjection,Matrix.mul_diagonal]
  by_cases hj : j=z
  · subst j
    simp [hm]
  · simp [hj]

#print axioms differential_column
#print axioms differential_row
#print axioms homotopy_column
#print axioms homotopy_row
#print axioms constantProjection
#print axioms annihilate_left
#print axioms annihilate_right

end Verification.ZeroWeightMatrixBlock
