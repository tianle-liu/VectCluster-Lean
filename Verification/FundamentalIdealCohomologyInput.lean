/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictNisnevichInput
import Verification.ChowWittFiberProductInput
import Verification.ExactCoefficientComparison
import Mathlib.FieldTheory.Perfect

/-!
# Fundamental Ideal Cohomology Input

Uniform ordinary fundamental-ideal/Milnor coefficient theory.
The exact sequence is 0→I^(j+1)→I^j→K^M_j/2→0. Diagonal Milnor
cohomology is CH^j/2 and cohomology above its Gersten length j vanishes.
At j=q=0 the usual rank-parity map is surjective (locally constant
parities are represented by rank-one forms on the open/closed components).
No exchange scheme, coordinate complex or desired I→W result is an input.
-/
noncomputable section
namespace Verification.FundamentalIdealCohomologyInput
open CategoryTheory AlgebraicGeometry
variable {M : Type*} (T : StrictNisnevichInput.Theory M)
variable (k : Type) [Field k] (IP KM : ℕ → M) (W : M)

structure Theory where
  inclusion : ∀ (R : Type) [CommRing R] [Algebra k R] [Algebra.Smooth k R] (j q : ℕ),
    T.cohomology (Spec (CommRingCat.of R)) (IP (j+1)) q →+
      T.cohomology (Spec (CommRingCat.of R)) (IP j) q
  quotient : ∀ (R : Type) [CommRing R] [Algebra k R] [Algebra.Smooth k R] (j q : ℕ),
    T.cohomology (Spec (CommRingCat.of R)) (IP j) q →+
      T.cohomology (Spec (CommRingCat.of R)) (KM j) q
  connecting : ∀ (R : Type) [CommRing R] [Algebra k R] [Algebra.Smooth k R] (j q : ℕ),
    T.cohomology (Spec (CommRingCat.of R)) (KM j) q →+
      T.cohomology (Spec (CommRingCat.of R)) (IP (j+1)) (q+1)
  toW : ∀ (R : Type) [CommRing R] [Algebra k R] [Algebra.Smooth k R] (j q : ℕ),
    T.cohomology (Spec (CommRingCat.of R)) (IP j) q →+
      T.cohomology (Spec (CommRingCat.of R)) W q

variable (Q : Theory T k IP KM W) (CH : Scheme → ℕ → AddCommGrp)

structure Standard [PerfectField k] (h2 : (2 : k) ≠ 0) : Prop where
  left_exact : ∀ (R : Type) [CommRing R] [Algebra k R] [Algebra.Smooth k R] (j q : ℕ),
    Function.Exact (Q.quotient R j q) (Q.connecting R j q)
  middle_exact : ∀ (R : Type) [CommRing R] [Algebra k R] [Algebra.Smooth k R] (j q : ℕ),
    Function.Exact (Q.connecting R j q) (Q.inclusion R j (q+1))
  right_exact : ∀ (R : Type) [CommRing R] [Algebra k R] [Algebra.Smooth k R] (j q : ℕ),
    Function.Exact (Q.inclusion R j q) (Q.quotient R j q)
  above : ∀ (R : Type) [CommRing R] [Algebra k R] [Algebra.Smooth k R] (j q : ℕ),
    j < q → Subsingleton (T.cohomology (Spec (CommRingCat.of R)) (KM j) q)
  diagonal : ∀ (R : Type) [CommRing R] [Algebra k R] [Algebra.Smooth k R] (j : ℕ),
    Nonempty (T.cohomology (Spec (CommRingCat.of R)) (KM j) j ≃+
      ChowWittFiberProductInput.modTwo (CH (Spec (CommRingCat.of R)) j))
  parity : ∀ (R : Type) [CommRing R] [Algebra k R] [Algebra.Smooth k R],
    Function.Surjective (Q.quotient R 0 0)
  zero_bijective : ∀ (R : Type) [CommRing R] [Algebra k R] [Algebra.Smooth k R] (q : ℕ),
    Function.Bijective (Q.toW R 0 q)
  inclusion_toW : ∀ (R : Type) [CommRing R] [Algebra k R] [Algebra.Smooth k R] (j q : ℕ),
    Q.toW R (j+1) q = (Q.toW R j q).comp (Q.inclusion R j q)

#print axioms Theory
#print axioms Standard
end Verification.FundamentalIdealCohomologyInput
