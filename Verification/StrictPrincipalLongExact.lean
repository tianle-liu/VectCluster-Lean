/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictNisnevichInput

/-!
# Strict Principal Long Exact

Four consecutive terms of the ordinary purity localization sequence
for any regular principal equation with smooth zero locus. The equation
trivializes the normal line. This is a uniform reference interface and
does not assume a dimension bound for any exchange variety.
-/
noncomputable section
namespace Verification.StrictPrincipalLongExact
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
variable {M : Type u} (T : StrictNisnevichInput.Theory M)

structure FourTerm (A : Type) [CommRing A] (f : A) (F : M) (q : ℕ) where
  push : T.cohomology (Spec (CommRingCat.of (A ⧸ Ideal.span {f}))) (T.contract F) q ⟶
    T.cohomology (Spec (CommRingCat.of A)) F (q+1)
  restriction : T.cohomology (Spec (CommRingCat.of A)) F (q+1) ⟶
    T.cohomology (Spec (CommRingCat.of (Localization.Away f))) F (q+1)
  residue : T.cohomology (Spec (CommRingCat.of (Localization.Away f))) F (q+1) ⟶
    T.cohomology (Spec (CommRingCat.of (A ⧸ Ideal.span {f}))) (T.contract F) (q+1)
  left_comp : push ≫ restriction = 0
  right_comp : restriction ≫ residue = 0
  left_exact : (ShortComplex.mk push restriction left_comp).Exact
  right_exact : (ShortComplex.mk restriction residue right_comp).Exact

structure Standard (k : Type) [Field k] where
  sequence : ∀ (A : Type) [CommRing A] [Algebra k A] [Algebra.Smooth k A]
    (f : A), IsSMulRegular A f → Algebra.Smooth k (A ⧸ Ideal.span {f}) →
    ∀ (F : M) (q : ℕ), FourTerm T A f F q

#print axioms FourTerm
#print axioms Standard
end Verification.StrictPrincipalLongExact
