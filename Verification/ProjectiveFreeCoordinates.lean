/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ProjectiveRankSum
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.Finiteness.Prod

/-!
# Projective Free Coordinates

An actually free finite projective module of prescribed local rank
has the claimed finite coordinate basis. Adding one trivial line has
exactly the incremented rank, so rank-three freeness gives the displayed
stable isomorphism for each rank-two bundle.
-/
noncomputable section
namespace Verification.ProjectiveFreeCoordinates
open Verification.ActualProjectiveSplitting
variable {R : Type} [CommRing R] [IsDomain R]

theorem stalk_rank (P : Bundle R) (p : PrimeSpectrum R) :
    Module.rankAtStalk P.object p=Module.finrank R P.object := by
  letI : FaithfulSMul R (Localization.AtPrime p.asIdeal) :=
    (faithfulSMul_iff_algebraMap_injective R (Localization.AtPrime p.asIdeal)).mpr
      (IsLocalization.injective (Localization.AtPrime p.asIdeal)
        p.asIdeal.primeCompl_le_nonZeroDivisors)
  exact (IsLocalizedModule.isBaseChange p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl P.object)).finrank_eq

theorem finrank_eq (P : Bundle R) {r : ℕ} (hr : HasRank P r) : Module.finrank R P.object=r := by
  let p : PrimeSpectrum R := ⟨⊥,Ideal.bot_prime⟩
  exact (stalk_rank P p).symm.trans (hr p)

def freeEquiv (P : Bundle R) {r : ℕ} (hr : HasRank P r) (hf : Trivial P) :
    P.object ≃ₗ[R] (Fin r → R) := by
  letI := P.finite
  letI : Module.Free R P.object := hf
  exact (Module.finBasisOfFinrankEq R P.object (finrank_eq P hr)).equivFun

def line : Bundle R where
  object := ModuleCat.of R R
  finite := inferInstance
  projective := inferInstance

theorem line_rank : HasRank (line (R := R)) 1 := by
  intro p
  rw [stalk_rank]
  exact Module.finrank_self R

def sum (P Q : Bundle R) : Bundle R := by
  letI := P.finite
  letI := Q.finite
  letI := P.projective
  letI := Q.projective
  exact ⟨ModuleCat.of R (P.object × Q.object),
    inferInstanceAs (Module.Finite R (P.object × Q.object)),
    inferInstanceAs (Module.Projective R (P.object × Q.object))⟩

omit [IsDomain R] in
theorem sum_rank {P Q : Bundle R} {r s : ℕ} (hP : HasRank P r) (hQ : HasRank Q s) :
    HasRank (sum P Q) (r+s) := by
  intro p
  rw [ProjectiveRankSum.rank_sum (sum P Q) P Q (LinearEquiv.refl R (P.object × Q.object)),hP p,hQ p]

theorem one_line_stable (hthree : ∀ P : Bundle R,HasRank P 3 → Trivial P)
    (P : Bundle R) (hr : HasRank P 2) : Nonempty ((P.object × R) ≃ₗ[R] (Fin 3 → R)) := by
  have hs : HasRank (sum P line) 3 := sum_rank hr line_rank
  exact ⟨freeEquiv (sum P line) hs (hthree _ hs)⟩

#print axioms stalk_rank
#print axioms finrank_eq
#print axioms freeEquiv
#print axioms line
#print axioms line_rank
#print axioms sum
#print axioms sum_rank
#print axioms one_line_stable
end Verification.ProjectiveFreeCoordinates
