/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictCohomologicalDimension
import Verification.ProjectiveConstantRank

/-!
# Nisnevich Splitting Input

Ordinary cited input: Asok--Fasel, Vector bundles on algebraic
varieties, ICM 2022, Theorem 1.1
(https://ems.press/content/book-chapter-files/33191).
A rank above the A¹-cohomological dimension splits off one free line.
This is uniform for all smooth affine algebras and does not assume
Picard vanishing, iteration, or any exchange variety conclusion.
-/
namespace Verification.NisnevichSplittingInput
open Verification.ActualProjectiveSplitting
universe u
variable {M : Type u} (T : StrictNisnevichInput.Theory M)
variable (k : Type) [Field k]
structure Standard where
  split : ∀ (A : Type) [CommRing A] [Algebra k A] [Algebra.Smooth k A]
    (d : ℕ), StrictCohomologicalDimension.Bound T A d →
    ∀ (r : ℕ), d < r+1 → ∀ (P : Bundle A), HasRank P (r+1) →
    ∃ Q : Bundle A, HasRank Q r ∧ Nonempty (P.object ≃ₗ[A] (Q.object × A))

#print axioms Standard
end Verification.NisnevichSplittingInput
