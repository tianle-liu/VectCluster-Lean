/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GradedMilnorWittScalarNaturality
import Verification.GradedMilnorWittLaurentWords

/-!
# Graded Milnor Witt Residue Scalar

Actual Laurent contraction respects right multiplication by base
coefficients, derived from the constructive Laurent word decomposition.
-/
noncomputable section
namespace Verification.GradedMilnorWittResidueScalar
open CategoryTheory AlgebraicGeometry
open Verification.GradedMilnorWittScalarNaturality
variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (D : GradedMilnorWittSheaf.Standard site N)
variable (K : StandardThomContractionNormalization.Grading R site N)
variable (hs : Algebra.Smooth R S)
variable (P : GradedMilnorWittLaurent.Standard R site N D K)
include P

theorem coefficient_mul (a : D.Total (CommRingCat.of (LaurentBasepoint.Laurent S)))
    (b : D.Total (CommRingCat.of R)) :
    GradedMilnorWittLaurent.residue R site N D K S hs (a*scalar R (LaurentBasepoint.Laurent S) site N D b)=
      GradedMilnorWittLaurent.residue R site N D K S hs a*scalar R S site N D b := by
  have h := naturality R S (LaurentBasepoint.Laurent S) site N D (LaurentBasepoint.coefficient R S) b
  change GradedMilnorWittLaurent.coefficient R site N D S (scalar R S site N D b)=
    scalar R (LaurentBasepoint.Laurent S) site N D b at h
  rw [← h]
  exact GradedMilnorWittLaurentWords.residue_coefficient_mul R S site N D K hs P a (scalar R S site N D b)

#print axioms coefficient_mul
end Verification.GradedMilnorWittResidueScalar
