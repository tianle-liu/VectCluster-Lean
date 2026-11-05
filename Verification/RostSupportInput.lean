/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RostAffineInput
import Verification.CoordinateKoszulClass
import Verification.OneRowConvergence
import Verification.PrimeIndependentHeight

/-!
# Rost Support Input

The ordinary support spectral sequence for regular coordinate
strata on a smooth affine scheme. Its abutment is the actual cycle
complex from RostAffineInput. The input is uniform in the affine
algebra and coordinates: no exchange matrix, acyclicity, degeneration,
component presentation, or Chow vanishing is assumed.
-/
noncomputable section
namespace Verification.RostSupportInput
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable (T : RostAffineInput.Theory)
variable (A V : Type) [CommRing A] [Fintype V] [DecidableEq V]
variable (x : V → A) (Allowed : Finset V → Prop) (s : ℤ)

abbrev Layer (r q : ℕ) := AddCommGrp.of
  (∀ I : PrimeLayerCover.Index Allowed r,
    (T.cycles (Spec (CommRingCat.of (PrimeStratumPresentation.ClosedRing x I.val)))
      (s-r)).homology q)

structure Data where
  pages : OneRowSequence.Pages AddCommGrp
  first : ∀ p q : ℕ,pages.E 1 p q ≅ Layer T A V x Allowed s p q
  negative_p : ∀ p q : ℤ,p<0 → IsZero (pages.E 1 p q)
  negative_q : ∀ p q : ℤ,q<0 → IsZero (pages.E 1 p q)
  convergence : OneRowConvergence.Input pages
    (fun q => (T.cycles (Spec (CommRingCat.of A)) s).homology q)
  row : CochainComplex AddCommGrp ℕ
  rowTerm : ∀ p,row.X p ≅ Layer T A V x Allowed s p 0
  rowHomology : ∀ p,row.homology p ≅ pages.E 2 p 0

structure Theory where
  sequence : ∀ (k A V : Type) [Field k] [CommRing A] [Algebra k A]
    [Algebra.Smooth k A] [Fintype V] [DecidableEq V]
    (x : V → A) (Allowed : Finset V → Prop),
    (∀ p : PrimeSpectrum A,Allowed (PrimeCoordinateFiltration.zeroSet x p)) →
    (∀ I,Allowed I → RingTheory.Sequence.IsWeaklyRegular
      (PrimeStratumPresentation.OpenRing x I)
      ((CoordinateKoszulClass.equations A V x I).map
        (algebraMap A (PrimeStratumPresentation.OpenRing x I)))) →
    ∀ s : ℤ,Data T A V x Allowed s

#print axioms Layer
#print axioms Data
#print axioms Theory
end Verification.RostSupportInput
