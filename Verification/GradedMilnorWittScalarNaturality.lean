/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GradedMilnorWittSheaf

/-!
# Graded Milnor Witt Scalar Naturality

Base coefficients commute with all actual algebra pullbacks because
those total pullbacks are built from the sheaf functor.
-/
noncomputable section
namespace Verification.GradedMilnorWittScalarNaturality
open CategoryTheory AlgebraicGeometry
variable (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
variable (site : GrothendieckTopology Scheme.{0}) (N : ℤ → Sheaf site (ModuleCat.{0} ℤ))
variable (D : GradedMilnorWittSheaf.Standard site N)

def scalar : D.Total (CommRingCat.of R) →+* D.Total (CommRingCat.of S) :=
  GradedMilnorWittSheaf.pullback site N D (S := CommRingCat.of R) (T := CommRingCat.of S) (algebraMap R S)

theorem naturality (f : S →ₐ[R] T) (a : D.Total (CommRingCat.of R)) :
    GradedMilnorWittSheaf.pullback site N D (S := CommRingCat.of S) (T := CommRingCat.of T) f.toRingHom
      (scalar R S site N D a)=scalar R T site N D a := by
  have h : (GradedMilnorWittSheaf.pullback site N D (S := CommRingCat.of S) (T := CommRingCat.of T) f.toRingHom).comp
      (scalar R S site N D)=scalar R T site N D := by
    unfold scalar
    rw [← GradedMilnorWittSheaf.pullback_comp]
    exact congrArg (GradedMilnorWittSheaf.pullback site N D (S := CommRingCat.of R) (T := CommRingCat.of T)) f.comp_algebraMap
  exact RingHom.congr_fun h a

#print axioms scalar
#print axioms naturality
end Verification.GradedMilnorWittScalarNaturality
