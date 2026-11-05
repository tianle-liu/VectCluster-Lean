/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RostAffineInput
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Rost Principal Localization Input

The ordinary codimension-one localization boundary for Milnor cycle
cohomology, uniform in a smooth affine algebra and a regular parameter.
This is only the cited localization operation. Its identification with a
support-row block and its valuation normalization are separate obligations;
no coordinate residue value or component formula is included here.
-/
noncomputable section
namespace Verification.RostPrincipalLocalizationInput
open CategoryTheory AlgebraicGeometry
variable (T : RostAffineInput.Theory)

abbrev OpenRing (A : Type) [CommRing A] (t : A) := Localization.Away t
abbrev ClosedRing (A : Type) [CommRing A] (t : A) := A ⧸ Ideal.span {t}

/-- Ordinary localization for the regular principal closed immersion.
The parameter need not be prime and the closed scheme need not be connected.
The field, smoothness, and regularity are hypotheses of the cited theorem. -/
structure Theory where
  boundary : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A]
    [Algebra.Smooth k A] (t : A),IsRegular t → ∀ s : ℤ,
    (T.cycles (Spec (CommRingCat.of (OpenRing A t))) s).homology 0 ⟶
      (T.cycles (Spec (CommRingCat.of (ClosedRing A t))) (s-1)).homology 0

#print axioms OpenRing
#print axioms ClosedRing
#print axioms Theory
end Verification.RostPrincipalLocalizationInput
