/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PostnikovStabilization
import Verification.ForgetfulStabilization
import Verification.ProjectiveConstantRank

/-!
# Bundle Cohomological Range

Original bundle-range deductions for actual finite projective
modules, relative only to ordinary determinant identities and the
individual cited Postnikov stages. K_0 rank and coefficient cohomology
are the actual constructions, not abstract class predicates.
-/
noncomputable section
universe v
namespace Verification.BundleCohomologicalRange
open Verification.ActualProjectiveSplitting Verification.ProjectiveFreeCoordinates
variable {R : Type} [CommRing R] [IsDomain R]
variable (D : DeterminantStandardInput.Standard R) (N : OrientedLineStabilization.Naturality D)
variable (k : Type) [Field k] [Algebra R k]
variable (C : Type*) (cochains : C → CochainComplex AddCommGrp.{v} ℕ)
variable (S : ∀ r,2≤r → PostnikovStabilization.StandardStages D N C cochains r)
variable (hk : Function.Injective (ProjectiveFieldRank.rankMap R k))
variable {h : ℕ} (hc : PostnikovStabilization.Above C cochains h)

include S hk hc in
theorem free_above (P : Bundle R) {r : ℕ} (hr : HasRank P r) (hh : h<r) : Trivial P := by
  by_cases he : r=1
  · subst r
    exact StableOrientations.line_free_of_kzero D k hk P hr
  · have hi : ∀ j,max 2 (h+1)≤j → Function.Injective (RankedProjectiveClasses.stabilize R j) := by
      intro j hj
      exact ForgetfulStabilization.injective D N k hk
        (PostnikovStabilization.advance_bijective (S j (by omega)) hc (by omega)).injective
    exact ActualKZeroStability.free_above R k hk hi P hr (by omega)

include S hk hc in
theorem one_line_stable (hh : h≤2) (P : Bundle R) (hr : HasRank P 2) :
    Nonempty ((P.object × R) ≃ₗ[R] (Fin 3 → R)) :=
  ProjectiveFreeCoordinates.one_line_stable
    (fun Q hQ => free_above D N k C cochains S hk hc Q hQ (by omega)) P hr

include S hk hc in
theorem all_free (hh : h≤1) (P : Bundle R) : Trivial P := by
  obtain ⟨r,hr⟩ := ProjectiveConstantRank.exists_rank P
  by_cases hz : r=0
  · subst r
    exact ProjectiveZeroRank.trivial P hr
  by_cases ho : r=1
  · subst r
    exact StableOrientations.line_free_of_kzero D k hk P hr
  exact free_above D N k C cochains S hk hc P hr (by omega)

#print axioms free_above
#print axioms one_line_stable
#print axioms all_free
end Verification.BundleCohomologicalRange
