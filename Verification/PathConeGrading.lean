/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathConeCancellation
import Verification.PerturbedHomologyModel

/-!
# Path Cone Grading

Degreewise cone cancellation on actual integer-indexed complexes. The
auxiliary two-block filtration is proved directly from the block coordinates.
-/

namespace Verification.PathConeGrading

open Verification.PathConeBlocks Verification.FinitePerturbation Verification.GradedPerturbation
  Verification.PerturbedHomologyModel

variable {R : Type*} [CommRing R] {ι κ : Type*}

def blockDegree (a : ι → ℤ) (b : κ → ℤ) : ι ⊕ κ → ℤ := Sum.elim a b

def blockWeight : ι ⊕ κ → ℕ := Sum.elim (fun _ => 1) (fun _ => 0)

theorem diagonal_homogeneous (a : ι → ℤ) (b : κ → ℤ) (d : ℤ)
    (A : Matrix ι ι R) (B : Matrix κ κ R) (hA : Homogeneous a d A) (hB : Homogeneous b d B) :
    Homogeneous (blockDegree a b) d (diagonal A B) := by
  intro i j h
  cases i with
  | inl i =>
    cases j with
    | inl j => exact hA i j h
    | inr j => rfl
  | inr i =>
    cases j with
    | inl j => rfl
    | inr j => exact hB i j h

theorem upper_homogeneous (a : ι → ℤ) (b : κ → ℤ) (d : ℤ)
    (C : Matrix ι κ R) (hC : ∀ i j, a i ≠ b j+d → C i j=0) :
    Homogeneous (blockDegree a b) d (upper C) := by
  intro i j h
  cases i with
  | inl i =>
    cases j with
    | inl j => rfl
    | inr j => exact hC i j h
  | inr i => cases j <;> rfl

theorem weight_bound (i : ι ⊕ κ) : blockWeight i ≤ 1 := by cases i <;> simp [blockWeight]

theorem diagonal_weight (H : Matrix ι ι R) (K : Matrix κ κ R) :
    ∀ i j, blockWeight i ≠ blockWeight j → diagonal H K i j=0 := by
  intro i j h
  cases i <;> cases j <;> simp_all [blockWeight,diagonal,Matrix.fromBlocks]

theorem upper_weight (C : Matrix ι κ R) :
    ∀ i j, blockWeight i ≤ blockWeight j → upper C i j=0 := by
  intro i j h
  cases i <;> cases j <;> simp_all [blockWeight,upper,Matrix.fromBlocks]

section Finite
variable [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def gradedRetraction (a : ι → ℤ) (b : κ → ℤ)
    (A H : Matrix ι ι R) (B K : Matrix κ κ R) (C : Matrix ι κ R)
    (hdA : Homogeneous a 1 A) (hdB : Homogeneous b 1 B)
    (hdH : Homogeneous a (-1) H) (hdK : Homogeneous b (-1) K)
    (hdC : ∀ i j, a i ≠ b j+1 → C i j=0)
    (hA : A*A=0) (hB : B*B=0) (hC : A*C+C*B=0)
    (hH : H*H=0) (hK : K*K=0) (hHAH : H*A*H=H) (hKBK : K*B*K=K)
    (hAHA : A*H*A=A) (hBKB : B*K*B=B) :
    GradedRetraction (blockDegree a b) (diagonal A B+upper C)
      (pureProjection (diagonal A B) (diagonal H K)) := by
  apply filteredRetraction (blockDegree a b) (diagonal A B) (diagonal H K) (upper C)
    (diagonal_homogeneous a b 1 A B hdA hdB)
    (diagonal_homogeneous a b (-1) H K hdH hdK)
    (upper_homogeneous a b 1 C hdC) _ _ _ _ (cone_square A B C hA hB hC)
    blockWeight 1 weight_bound (diagonal_weight H K) (upper_weight C)
  · rw [diagonal_mul,hA,hB,diagonal_zero]
  · rw [diagonal_mul,hH,hK,diagonal_zero]
  · rw [diagonal_mul,diagonal_mul,hHAH,hKBK]
  · rw [diagonal_mul,diagonal_mul,hAHA,hBKB]

end Finite

#print axioms blockDegree
#print axioms blockWeight
#print axioms diagonal_homogeneous
#print axioms upper_homogeneous
#print axioms weight_bound
#print axioms diagonal_weight
#print axioms upper_weight
#print axioms gradedRetraction

end Verification.PathConeGrading
