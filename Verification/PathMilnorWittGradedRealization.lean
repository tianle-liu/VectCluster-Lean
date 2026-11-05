/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathCoefficientGradedRealization
import Verification.PathMilnorWittCoefficients
import Verification.GradedMilnorWittDegreeSpaces

/-!
# Path Milnor Witt Graded Realization

Formal homogeneous path coefficients have their asserted degrees in
the actual Milnor-Witt section ring. This follows internally from the
coaction and the ordinary grading of symbols and multiplication.
-/
noncomputable section
namespace Verification.PathMilnorWittGradedRealization
open CategoryTheory AlgebraicGeometry
open Verification.GradedSectionTotal Verification.SheafGradedLaurentResidue
open Verification.GradedMilnorWittHomogeneity
variable {site : GrothendieckTopology Scheme.{0}} {N : ℤ → Sheaf site (ModuleCat.{0} ℤ)}
variable {D : GradedMilnorWittSheaf.Standard site N}
variable (P : Standard site N D) (S : CommRingCat.{0})
include P

theorem intCast (z : ℤ) : Homogeneous site N D S 0 (z : D.Total S) := by
  have hone : (1 : D.Total S) ∈ GradedMilnorWittDegreeSpaces.space site N D S 0 :=
    ⟨P.oneSection S,P.one_value S⟩
  have hz := (GradedMilnorWittDegreeSpaces.space site N D S 0).zsmul_mem hone z
  simpa only [zsmul_eq_mul,mul_one] using hz

theorem homogeneous {c : PathCoefficientRing.Coeff} {k : ℤ}
    (h : PathCoefficientGrading.Homogeneous k c) :
    Homogeneous site N D S k (PathMilnorWittCoefficients.realize (D.symbols S).toCoefficients c) := by
  apply PathCoefficientGradedRealization.homogeneous
    (PathMilnorWittCoefficients.realize (D.symbols S).toCoefficients)
    (Homogeneous site N D S)
    (fun k => GradedMilnorWittHomogeneity.zero S k) (intCast P S)
    (fun _ _ _ => GradedMilnorWittHomogeneity.add) ?_ ?_ h
  · intro k a ha
    rw [PathMilnorWittCoefficients.realize_g]
    simpa only [add_zero] using GradedMilnorWittHomogeneity.mul P ha (GradedMilnorWittHomogeneity.g P S)
  · intro k a ha
    rw [PathMilnorWittCoefficients.realize_rho]
    exact GradedMilnorWittHomogeneity.mul P ha (GradedMilnorWittHomogeneity.rho P S)

#print axioms intCast
#print axioms homogeneous
end Verification.PathMilnorWittGradedRealization
