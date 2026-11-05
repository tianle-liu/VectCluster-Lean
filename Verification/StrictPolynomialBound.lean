/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StrictCohomologicalDimension
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Strict Polynomial Bound

Homotopy invariance for the actual polynomial algebra, at each
cohomological dimension bound.
-/
noncomputable section
namespace Verification.StrictPolynomialBound
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Verification.StrictCohomologicalDimension
universe u
variable {M : Type u} (T : StrictNisnevichInput.Theory M)
variable (k : Type) [Field k] (P : StrictNisnevichInput.Standard T k)
variable (A : Type) [CommRing A] [Algebra k A] [Algebra.Smooth k A]
include P k in
theorem bound (d : ℕ) (h : Bound T A d) : Bound T (Polynomial A) d := by
  apply of_equiv T (MvPolynomial.pUnitAlgEquiv A).symm.toRingEquiv d
  intro F q hq
  exact IsZero.of_iso (h F q hq) (P.affine A PUnit F q)

#print axioms bound
end Verification.StrictPolynomialBound
