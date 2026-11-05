/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Tactic

/-!
# Exchange Geometry

The zero-set argument in manuscript.tex:369–377, for acyclic exchange
equations in a chosen topological ordering. Frozen monomials are absorbed
in the nonzero coefficients. Edge weights in the two directions may differ,
as for a skew-symmetrizable principal matrix, but their supports agree.
-/

namespace Verification.ExchangeGeometry

open Finset

variable {K : Type*} {n : ℕ}

section Definitions

variable [CommRing K]

def earlierMonomial (w : Fin n → Fin n → ℕ) (x : Fin n → K) (i : Fin n) : K :=
  ∏ j, x j ^ (if j < i then w j i else 0)

def laterMonomial (w : Fin n → Fin n → ℕ) (x : Fin n → K) (i : Fin n) : K :=
  ∏ j, x j ^ (if i < j then w i j else 0)

/-- Exchange equations with nonzero scalar/frozen coefficients. -/
def ExchangeEquations (u v : Fin n → Fin n → ℕ)
    (x y c d : Fin n → K) : Prop :=
  ∀ i, x i * y i = c i * earlierMonomial u x i + d i * laterMonomial v x i

end Definitions

section Fields

variable [Field K]

/-- A vanishing coordinate has no vanishing later neighbor. -/
theorem zero_forces_later_nonzero
    (u v : Fin n → Fin n → ℕ) (x y c d : Fin n → K)
    (hsupport : ∀ i j, u i j = 0 ↔ v i j = 0)
    (hc : ∀ i, c i ≠ 0)
    (he : ExchangeEquations u v x y c d) :
    ∀ i, x i = 0 → ∀ j, i < j → v i j ≠ 0 → x j ≠ 0 := by
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    intro hi j hij hv
    have hu : earlierMonomial u x i ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro a _
      by_cases hai : a < i
      · simp only [if_pos hai]
        by_cases hua : u a i = 0
        · simp [hua]
        · apply pow_ne_zero
          intro hxa
          exact (ih a hai hxa i hai (mt (hsupport a i).mpr hua)) hi
      · simp [hai]
    have hl : laterMonomial v x i ≠ 0 := by
      intro hz
      have h := he i
      rw [hi, zero_mul, hz, mul_zero, add_zero] at h
      exact (mul_ne_zero (hc i) hu) h.symm
    have hj := Finset.prod_ne_zero_iff.mp hl j (Finset.mem_univ j)
    simp only [if_pos hij] at hj
    intro hz
    apply hj
    simp [hz, hv]

/-- The simultaneous zero set is independent for the support graph. -/
theorem zero_set_independent
    (u v : Fin n → Fin n → ℕ) (x y c d : Fin n → K)
    (hsupport : ∀ i j, u i j = 0 ↔ v i j = 0)
    (hc : ∀ i, c i ≠ 0)
    (he : ExchangeEquations u v x y c d)
    (i j : Fin n) (hi : x i = 0) (hj : x j = 0) :
    (i < j → v i j = 0) ∧ (j < i → v j i = 0) := by
  constructor
  · intro hij
    by_contra hv
    exact zero_forces_later_nonzero u v x y c d hsupport hc he i hi j hij hv hj
  · intro hji
    by_contra hv
    exact zero_forces_later_nonzero u v x y c d hsupport hc he j hj i hji hv hi

#print axioms zero_forces_later_nonzero
#print axioms zero_set_independent

end Fields

end Verification.ExchangeGeometry

-- Explicit dependency audit of the early module constructions.
#print axioms Verification.ExchangeGeometry.ExchangeEquations
#print axioms Verification.ExchangeGeometry.earlierMonomial
#print axioms Verification.ExchangeGeometry.laterMonomial
