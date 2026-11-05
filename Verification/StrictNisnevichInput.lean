/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RostEdgelessPrincipalInput

/-!
# Strict Nisnevich Input

Uniform reference interface for Nisnevich cohomology of strictly
A¹-invariant coefficient sheaves and their contractions. The usual
homotopy invariance, field vanishing, and principal purity localization
are the only reference facts. No exchange algebra or vanishing statement
for such an algebra is included in the interface.
-/
noncomputable section
namespace Verification.StrictNisnevichInput
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
variable (M : Type u)

structure Theory where
  cohomology : Scheme → M → ℕ → AddCommGrp
  contract : M → M
  iso : ∀ {X Y : Scheme}, (X ≅ Y) → ∀ (F : M) (q : ℕ),
    cohomology X F q ≅ cohomology Y F q

variable {M} (T : Theory M)

structure Sequence (A : Type) [CommRing A] (f : A) (F : M) (q : ℕ) where
  sequence : ShortComplex AddCommGrp
  source : sequence.X₁ ≅ T.cohomology (Spec (CommRingCat.of A)) F q
  middle : sequence.X₂ ≅ T.cohomology (Spec (CommRingCat.of (Localization.Away f))) F q
  target : sequence.X₃ ≅ T.cohomology (Spec (CommRingCat.of (A ⧸ Ideal.span {f}))) (T.contract F) q
  exact : sequence.Exact

structure Standard (k : Type) [Field k] where
  field_zero : ∀ (F : M) (q : ℕ), 0 < q → IsZero (T.cohomology (Spec (CommRingCat.of k)) F q)
  affine : ∀ (A ι : Type) [CommRing A] [Algebra k A]
    [Algebra.Smooth k A] [Fintype ι] (F : M) (q : ℕ),
    T.cohomology (Spec (CommRingCat.of (MvPolynomial ι A))) F q ≅
      T.cohomology (Spec (CommRingCat.of A)) F q
  principal : ∀ (A : Type) [CommRing A] [Algebra k A]
    [Algebra.Smooth k A] (f : A), IsSMulRegular A f →
    Algebra.Smooth k (A ⧸ Ideal.span {f}) → ∀ (F : M) (q : ℕ), Sequence T A f F q

#print axioms Theory
#print axioms Sequence
#print axioms Standard
end Verification.StrictNisnevichInput
