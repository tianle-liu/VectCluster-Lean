/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathLattice

/-!
# Path Orientation Signs

Every single-arrow orientation of a path is related to its linear
skew adjacency matrix by explicit integral diagonal vertex signs. This
is a lattice computation, independent of cluster mutation invariance.
-/

namespace Verification.PathOrientationSigns
open Finset

def vertexSign (a : ℕ → ℤˣ) (n : ℕ) : ℤˣ := ∏ i ∈ range n,a i

theorem vertexSign_succ (a : ℕ → ℤˣ) (n : ℕ) : vertexSign a (n+1)=vertexSign a n*a n :=
  prod_range_succ _ n

theorem adjacent (a : ℕ → ℤˣ) (n : ℕ) : vertexSign a n*vertexSign a (n+1)=a n := by
  rw [vertexSign_succ,← mul_assoc,Int.units_mul_self,one_mul]

theorem adjacent_int (a : ℕ → ℤˣ) (n : ℕ) :
    (vertexSign a n:ℤ)*(vertexSign a (n+1):ℤ)=(a n:ℤ) :=
  congrArg Units.val (adjacent a n)

/-- The actual signed skew adjacency matrix for arbitrary edge orientations. -/
def matrix (a : ℕ → ℤˣ) (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j=>
  (if j.val=i.val+1 then (a i.val:ℤ) else 0) -
    (if i.val=j.val+1 then (a j.val:ℤ) else 0)

theorem matrix_conjugacy (a : ℕ → ℤˣ) (n : ℕ) (i j : Fin n) :
    matrix a n i j=(vertexSign a i.val:ℤ)*PathLattice.pathMatrix n i j*(vertexSign a j.val:ℤ) := by
  by_cases h : j.val=i.val+1
  · have h' : i.val≠j.val+1 := by omega
    simp only [matrix,PathLattice.pathMatrix,if_pos h,if_neg h',sub_zero,mul_one]
    rw [h,adjacent_int]
  · by_cases h' : i.val=j.val+1
    · simp only [matrix,PathLattice.pathMatrix,if_neg h,if_pos h',zero_sub,mul_neg,mul_one,neg_mul]
      rw [h',mul_comm,adjacent_int]
    · simp [matrix,PathLattice.pathMatrix,h,h']

theorem matrix_nonedge (a : ℕ → ℤˣ) (n : ℕ) (i j : Fin n)
    (h : j.val≠i.val+1) (h' : i.val≠j.val+1) : matrix a n i j=0 := by
  simp [matrix,h,h']

#print axioms vertexSign
#print axioms vertexSign_succ
#print axioms adjacent
#print axioms adjacent_int
#print axioms matrix
#print axioms matrix_conjugacy
#print axioms matrix_nonedge

end Verification.PathOrientationSigns
