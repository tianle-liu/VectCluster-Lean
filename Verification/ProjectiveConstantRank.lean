/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ProjectiveZeroRank

/-!
# Projective Constant Rank

Finite projective modules over the domain coordinate rings have an
actual constant local rank. Thus the repeated-splitting argument covers
all projective modules, with no unproved rank-zero base case.
-/
noncomputable section
namespace Verification.ProjectiveConstantRank
open Verification.ActualProjectiveSplitting
variable {R : Type} [CommRing R] [IsDomain R]

theorem exists_rank (P : Bundle R) : ∃ r : ℕ,HasRank P r := by
  letI := P.finite
  letI := P.projective
  letI : Module.FinitePresentation R P.object := Module.finitePresentation_of_projective R P.object
  obtain ⟨r,hr⟩ := (Module.isLocallyConstant_rankAtStalk (R := R) (M := P.object)).exists_eq_const
  exact ⟨r,fun p => congrFun hr p⟩

theorem all_free (hline : ∀ P : Bundle R,HasRank P 1 → Trivial P)
    (hsplit : SplitsAboveOne (R := R)) (P : Bundle R) : Trivial P := by
  obtain ⟨r,hr⟩ := exists_rank P
  exact free_of_splitting ProjectiveZeroRank.trivial hline hsplit r P hr

#print axioms exists_rank
#print axioms all_free
end Verification.ProjectiveConstantRank
