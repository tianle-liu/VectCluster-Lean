/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualStableCancellation
import Verification.ProjectiveRankCriterion

/-!
# Actual K Zero Stability

The hypothesis that the actual Grothendieck-group rank map is
injective implies stable freeness of each actual projective bundle.
The local rank determines the rank of the resulting free coordinates.
-/
noncomputable section
namespace Verification.ActualKZeroStability
open Verification.ActualProjectiveSplitting Verification.ProjectiveFreeCoordinates
open Verification.RankedProjectiveClasses Verification.ActualStableCancellation
variable (R : Type) [CommRing R] (k : Type) [Field k] [Algebra R k]

theorem stablyFree (hi : Function.Injective (ProjectiveFieldRank.rankMap R k))
    (P : Bundle R) : StablyFree R P := by
  obtain ⟨r,n,⟨e⟩⟩ := ProjectiveRankCriterion.stably_free_of_rankMap_injective R k hi
    (projectiveObject R P)
  exact ⟨n,Module.Free.of_equiv e.symm⟩

variable [IsDomain R]

def stableCoordinates (P : Bundle R) {r : ℕ} (hr : HasRank P r)
    (hs : StablyFree R P) :
    (P.object × (Fin hs.choose → R)) ≃ₗ[R] (Fin (r+hs.choose) → R) := by
  change (sum P (freeBundle R hs.choose)).object ≃ₗ[R] (Fin (r+hs.choose) → R)
  exact freeEquiv (sum P (freeBundle R hs.choose)) (sum_rank hr (freeBundle_rank R hs.choose))
    hs.choose_spec

theorem free_above {lower : ℕ}
    (hk : Function.Injective (ProjectiveFieldRank.rankMap R k))
    (hi : ∀ r,lower≤r → Function.Injective (stabilize R r))
    (P : Bundle R) {r : ℕ} (hr : HasRank P r) (hl : lower≤r) : Trivial P :=
  cancel_all R hi P hr hl (stablyFree R k hk P)

#print axioms stablyFree
#print axioms stableCoordinates
#print axioms free_above
end Verification.ActualKZeroStability
