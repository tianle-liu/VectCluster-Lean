/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualProjectiveSplitting
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Projective Zero Rank

For the actual domain coordinate rings in the manuscript, the rank-zero
base case is proved locally at every prime and then descended by support.
-/
noncomputable section
namespace Verification.ProjectiveZeroRank
open Verification.ActualProjectiveSplitting
variable {R : Type} [CommRing R] [IsDomain R]

theorem subsingleton (P : Bundle R) (hP : HasRank P 0) : Subsingleton P.object := by
  letI := P.finite
  letI := P.projective
  apply (Module.support_eq_empty_iff (R := R) (M := P.object)).mp
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro p
  apply Module.not_mem_support_iff.mpr
  letI : Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl P.object) :=
    Module.free_of_flat_of_isLocalRing
  exact (Module.finrank_zero_iff (R := Localization.AtPrime p.asIdeal)).mp (hP p)

theorem trivial (P : Bundle R) (hP : HasRank P 0) : Trivial P := by
  letI := subsingleton P hP
  exact inferInstanceAs (Module.Free R P.object)

#print axioms subsingleton
#print axioms trivial
end Verification.ProjectiveZeroRank
