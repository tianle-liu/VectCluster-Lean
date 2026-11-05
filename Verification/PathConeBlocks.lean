/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FinitePerturbation
import Mathlib.Data.Matrix.Block

/-!
# Path Cone Blocks

Literal two-block cone algebra for combining the already identified path
open and closed differentials. The off-diagonal correction has square zero.
-/

namespace Verification.PathConeBlocks

open Verification.FinitePerturbation

variable {R : Type*} [CommRing R]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def diagonal (A : Matrix ι ι R) (B : Matrix κ κ R) : Matrix (ι ⊕ κ) (ι ⊕ κ) R :=
  Matrix.fromBlocks A 0 0 B

def upper (C : Matrix ι κ R) : Matrix (ι ⊕ κ) (ι ⊕ κ) R := Matrix.fromBlocks 0 C 0 0

theorem diagonal_mul (A A' : Matrix ι ι R) (B B' : Matrix κ κ R) :
    diagonal A B*diagonal A' B'=diagonal (A*A') (B*B') := by
  simp only [diagonal,Matrix.fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add]

theorem upper_mul (C C' : Matrix ι κ R) : upper C*upper C'=0 := by
  simp only [upper,Matrix.fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,add_zero,Matrix.fromBlocks_zero]

theorem diagonal_upper (A : Matrix ι ι R) (B : Matrix κ κ R) (C : Matrix ι κ R) :
    diagonal A B*upper C=upper (A*C) := by
  simp only [diagonal,upper,Matrix.fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add]

theorem upper_diagonal (A : Matrix ι ι R) (B : Matrix κ κ R) (C : Matrix ι κ R) :
    upper C*diagonal A B=upper (C*B) := by
  simp only [diagonal,upper,Matrix.fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add]

omit [Fintype ι] [Fintype κ] in
theorem diagonal_zero : diagonal (0 : Matrix ι ι R) (0 : Matrix κ κ R)=0 := Matrix.fromBlocks_zero

theorem diagonal_projection [DecidableEq ι] [DecidableEq κ] (A H : Matrix ι ι R) (B K : Matrix κ κ R) :
    pureProjection (diagonal A B) (diagonal H K)=diagonal (pureProjection A H) (pureProjection B K) := by
  simp only [pureProjection,diagonal_mul]
  ext i j
  cases i <;> cases j <;> simp [diagonal,Matrix.fromBlocks,Matrix.one_apply,Matrix.sub_apply]

theorem cone_square (A : Matrix ι ι R) (B : Matrix κ κ R) (C : Matrix ι κ R)
    (hA : A*A=0) (hB : B*B=0) (hC : A*C+C*B=0) :
    (diagonal A B+upper C)*(diagonal A B+upper C)=0 := by
  have he : diagonal A B+upper C=Matrix.fromBlocks A C 0 B := by
    rw [diagonal,upper,Matrix.fromBlocks_add]
    simp only [add_zero,zero_add]
  rw [he,Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add,hA,hB,hC,Matrix.fromBlocks_zero]

theorem upper_homotopy_square (H : Matrix ι ι R) (K : Matrix κ κ R) (C : Matrix ι κ R) :
    (upper C*diagonal H K)*(upper C*diagonal H K)=0 := by
  rw [upper_diagonal,upper_mul]

theorem homotopy_upper_square (H : Matrix ι ι R) (K : Matrix κ κ R) (C : Matrix ι κ R) :
    (diagonal H K*upper C)*(diagonal H K*upper C)=0 := by
  rw [diagonal_upper,upper_mul]

theorem upper_homotopy_upper (H : Matrix ι ι R) (K : Matrix κ κ R) (C : Matrix ι κ R) :
    upper C*diagonal H K*upper C=0 := by
  rw [upper_diagonal,upper_mul]

#print axioms diagonal
#print axioms upper
#print axioms diagonal_mul
#print axioms upper_mul
#print axioms diagonal_upper
#print axioms upper_diagonal
#print axioms diagonal_zero
#print axioms diagonal_projection
#print axioms cone_square
#print axioms upper_homotopy_square
#print axioms homotopy_upper_square
#print axioms upper_homotopy_upper

end Verification.PathConeBlocks
