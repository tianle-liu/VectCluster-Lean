/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FlagNormalCoordinates
import Verification.PrincipalObjectPurity
import Verification.RelativeFlagOpenBoundary
import Verification.CoordinateLastRegular

/-!
# Principal Flag Comparison

An independently constructed iterated Thom comparison: first use the
actual normal-coordinate/quotient equivalence, then the fixed principal
purity comparison of the old closed stratum. Regularity and smoothness of
that principal pair are deduced from the full coordinate frame.
-/
noncomputable section
namespace Verification.PrincipalFlagComparison
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CochainComplex
open Verification.CoordinateFlag Verification.CoordinatePurityInput
universe w
variable {C : Type*} [Category C] [Abelian C] [HasBinaryBiproducts C] [HasDerivedCategory.{w} C]
variable (R A ι : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype ι] [DecidableEq ι]
variable (x : ι → A) (v : ι) (fullFrame : Frame R A ι x)

include fullFrame in
omit [DecidableEq ι] in
theorem parameter_regular : IsSMulRegular (ClosedOld A ι x v) (parameter A ι x v) :=
  CoordinateLastRegular.regular_after_others x v (fun l hl => (fullFrame.regular l hl).toIsWeaklyRegular)

include fullFrame in
omit [Fintype ι] [DecidableEq ι] in
theorem closed_smooth : Algebra.Smooth R (ClosedAll A ι x v) := by
  letI := fullFrame.closedSmooth
  exact Algebra.Smooth.of_equiv (CoordinateFlagTotalQuotient.equiv R A ι x v).symm

variable (G : Scheme ⥤ CochainComplex C ℤ)
variable (oldFrame : Frame R A (Old ι v) (oldCoordinate A ι x v))
variable (Q : PrincipalObjectPurity.Standard R (AffineRelativeThom.theory R (Old ι v) G)
  (AffineRelativeThom.theory R (FlagNormalCoordinates.Normals ι v) G ⋙ DerivedCategory.Q))

def comparison : normalThom A ι x G ≅
    DerivedCategory.Q.obj (mappingCone (RelativeFlagOpenBoundary.openArrow R A ι x v G)) :=
  FlagNormalCoordinates.thomIso R A ι x v G ≪≫
    Q.comparison (ClosedOld A ι x v) (parameter A ι x v) oldFrame.closedSmooth
      (closed_smooth R A ι x v fullFrame) (parameter_regular R A ι x v fullFrame)

#print axioms parameter_regular
#print axioms closed_smooth
#print axioms comparison
end Verification.PrincipalFlagComparison
