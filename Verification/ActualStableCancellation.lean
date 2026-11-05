/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RankedProjectiveClasses
import Verification.ProjectiveClasses

/-!
# Actual Stable Cancellation

Stable freeness and successive cancellation for actual finite
projective modules. The stabilizing free summand is eliminated one
actual trivial line at a time.
-/
noncomputable section
namespace Verification.ActualStableCancellation
open Verification.ActualProjectiveSplitting Verification.ProjectiveFreeCoordinates
open Verification.RankedProjectiveClasses
variable (R : Type) [CommRing R] [IsDomain R]

def projectiveObject (P : Bundle R) : ProjectiveClasses.Object R :=
  ⟨P.object,P.finite,P.projective⟩

def StablyFree (P : Bundle R) : Prop :=
  ∃ n : ℕ,Module.Free R (P.object × (Fin n → R))

omit [IsDomain R] in
theorem of_kzero (P : Bundle R) (r : ℕ)
    (he : ProjectiveClasses.completionClass R (projectiveObject R P)=
      ProjectiveClasses.completionClass R (ProjectiveClasses.of R (Fin r → R))) :
    StablyFree R P := by
  obtain ⟨n,⟨e⟩⟩ := ProjectiveClasses.stable_free_of_completionClass R _ r he
  exact ⟨n,Module.Free.of_equiv e.symm⟩

def oneMoreCoordinates (n : ℕ) : (R × (Fin n → R)) ≃ₗ[R] (Fin (n+1) → R) :=
  freeEquiv (sum line (freeBundle R n))
    (by simpa only [Nat.add_comm] using sum_rank (line_rank (R := R)) (freeBundle_rank R n))
    (inferInstanceAs (Module.Free R (R × (Fin n → R))))

def sumCoordinates (P : Bundle R) (n : ℕ) :
    ((P.object × R) × (Fin n → R)) ≃ₗ[R] (P.object × (Fin (n+1) → R)) :=
  (LinearEquiv.prodAssoc R P.object R (Fin n → R)).trans
    ((LinearEquiv.refl R P.object).prodCongr (oneMoreCoordinates R n))

theorem cancel_all {lower : ℕ}
    (hi : ∀ r,lower≤r → Function.Injective (stabilize R r))
    (P : Bundle R) {r : ℕ} (hr : HasRank P r) (hl : lower≤r)
    (hs : StablyFree R P) : Trivial P := by
  obtain ⟨n,hf⟩ := hs
  induction n generalizing P r with
  | zero =>
    let e : (P.object × (Fin 0 → R)) ≃ₗ[R] P.object :=
      (LinearEquiv.prodComm R P.object (Fin 0 → R)).trans
        (ProjectiveClasses.zeroProduct R (projectiveObject R P))
    exact Module.Free.of_equiv' hf e
  | succ n ih =>
    have hplus : Module.Free R ((P.object × R) × (Fin n → R)) :=
      Module.Free.of_equiv' hf (sumCoordinates R P n).symm
    have hp := ih (sum P line) (sum_rank hr line_rank) (by omega) hplus
    exact cancel_line R (hi r hl) P hr hp

theorem free_of_kzero {lower : ℕ}
    (hi : ∀ r,lower≤r → Function.Injective (stabilize R r))
    (P : Bundle R) {r : ℕ} (hr : HasRank P r) (hl : lower≤r)
    (he : ProjectiveClasses.completionClass R (projectiveObject R P)=
      ProjectiveClasses.completionClass R (ProjectiveClasses.of R (Fin r → R))) :
    Trivial P := cancel_all R hi P hr hl (of_kzero R P r he)

#print axioms projectiveObject
#print axioms StablyFree
#print axioms of_kzero
#print axioms oneMoreCoordinates
#print axioms sumCoordinates
#print axioms cancel_all
#print axioms free_of_kzero
end Verification.ActualStableCancellation
