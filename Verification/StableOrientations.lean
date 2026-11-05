/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.DeterminantStandardInput
import Verification.ActualKZeroStability

/-!
# Stable Orientations

Stable freeness supplies actual determinant orientations; in rank
one it implies freeness. Only the ordinary determinant identities are
external inputs, not these consequences or an orientability assertion.
-/
noncomputable section
namespace Verification.StableOrientations
open CategoryTheory Verification.ActualProjectiveSplitting
open Verification.ProjectiveFreeCoordinates Verification.RankedProjectiveClasses
open Verification.ActualStableCancellation
variable {R : Type} [CommRing R] [IsDomain R]
variable (D : DeterminantStandardInput.Standard R)

def orientation (P : Bundle R) {r : ℕ} (hr : HasRank P r) (hs : StablyFree R P) :
    P.object.exteriorPower r ≅ ModuleCat.of R R :=
  (DeterminantStandardInput.stabilization D P hr hs.choose).symm ≪≫
    (ModuleCat.exteriorPower.functor R (r+hs.choose)).mapIso
      (ActualKZeroStability.stableCoordinates R P hr hs).toModuleIso ≪≫
    D.freeVolume (r+hs.choose)

def oriented (P : Bundle R) {r : ℕ} (hr : HasRank P r) (hs : StablyFree R P) :
    ActualOrientations.Oriented R r := ⟨P,hr,orientation D P hr hs⟩

include D in
theorem line_free (P : Bundle R) (hr : HasRank P 1) (hs : StablyFree R P) : Trivial P := by
  let e : P.object ≅ ModuleCat.of R R :=
    (ModuleCat.exteriorPower.iso₁ P.object).symm ≪≫ orientation D P hr hs
  letI : Module.Free R (ModuleCat.of R R) := inferInstanceAs (Module.Free R R)
  exact Module.Free.of_equiv e.toLinearEquiv.symm

def of_kzero (k : Type) [Field k] [Algebra R k]
    (hk : Function.Injective (ProjectiveFieldRank.rankMap R k))
    (P : Bundle R) {r : ℕ} (hr : HasRank P r) : ActualOrientations.Oriented R r :=
  oriented D P hr (ActualKZeroStability.stablyFree R k hk P)

include D in
theorem line_free_of_kzero (k : Type) [Field k] [Algebra R k]
    (hk : Function.Injective (ProjectiveFieldRank.rankMap R k))
    (P : Bundle R) (hr : HasRank P 1) : Trivial P :=
  line_free D P hr (ActualKZeroStability.stablyFree R k hk P)

#print axioms orientation
#print axioms oriented
#print axioms line_free
#print axioms of_kzero
#print axioms line_free_of_kzero
end Verification.StableOrientations
