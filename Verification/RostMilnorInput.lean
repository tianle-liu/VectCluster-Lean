/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RostAffineInput
import Mathlib.RingTheory.Smooth.Basic

/-!
# Rost Milnor Input

Ordinary Milnor-cycle conventions: negative weights vanish and
diagonal cycle cohomology is the Chow group by rational equivalence.
Both statements are uniform in schemes/algebras; no cluster-space
Chow computation or vanishing is included.
-/
noncomputable section
namespace Verification.RostMilnorInput
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable (T : RostAffineInput.Theory)

structure NegativeWeights : Prop where
  zero : ∀ (X : Scheme) (s : ℤ),s<0 → IsZero ((T.cycles X s).homology 0)

structure ChowComparison (CH : Scheme → ℕ → AddCommGrp) where
  diagonal : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A]
    [Algebra.Smooth k A] (p : ℕ),
    CH (Spec (CommRingCat.of A)) p ≅ (T.cycles (Spec (CommRingCat.of A)) p).homology p

#print axioms NegativeWeights
#print axioms ChowComparison
end Verification.RostMilnorInput
