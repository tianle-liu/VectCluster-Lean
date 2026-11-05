/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RostAffineInput
import Verification.PrincipalConormal
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Rost Edgeless Principal Input

Uniform ordinary cycle-module facts: affine-bundle invariance and the
three consecutive terms H^q(A,M), H^q(D(f),M), H^q(V(f),M_{-1}) of the
localization sequence for a regular principal equation with smooth zero
locus. The equation supplies the normal framing. No exchange algebra,
product model, or vanishing conclusion occurs in these reference inputs.
-/
noncomputable section
namespace Verification.RostEdgelessPrincipalInput
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable (T : RostAffineInput.Theory)

structure Sequence (A : Type) [CommRing A] (f : A) (s : ℤ) (q : ℕ) where
  sequence : ShortComplex AddCommGrp
  source : sequence.X₁ ≅ (T.cycles (Spec (CommRingCat.of A)) s).homology q
  middle : sequence.X₂ ≅ (T.cycles (Spec (CommRingCat.of (Localization.Away f))) s).homology q
  target : sequence.X₃ ≅ (T.cycles (Spec (CommRingCat.of (A ⧸ Ideal.span {f}))) (s-1)).homology q
  exact : sequence.Exact

structure Standard where
  affine : ∀ (k A ι : Type) [Field k] [CommRing A] [Algebra k A]
    [Algebra.Smooth k A] [Fintype ι] (s : ℤ) (q : ℕ),
    (T.cycles (Spec (CommRingCat.of (MvPolynomial ι A))) s).homology q ≅
      (T.cycles (Spec (CommRingCat.of A)) s).homology q
  principal : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A]
    [Algebra.Smooth k A] (f : A), IsSMulRegular A f →
    Algebra.Smooth k (A ⧸ Ideal.span {f}) → ∀ (s : ℤ) (q : ℕ), Sequence T A f s q

#print axioms Sequence
#print axioms Standard
end Verification.RostEdgelessPrincipalInput
