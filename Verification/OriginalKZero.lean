/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalGZeroFiltration
import Verification.SmoothCartanInput
import Verification.RankFromCartan
import Verification.ActualKZeroStability
import Verification.CoherentUnit

/-!
# Original K Zero

The original exchange algebra's actual finite-projective K_0 is Z
by the constructed rank map, and every actual projective bundle is stably
free. The global G_0 filtration is proved in the imported module; the
only remaining inputs here are uniform ordinary reference theorems.
-/
noncomputable section
namespace Verification.OriginalKZero
open CategoryTheory AlgebraicGeometry
open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
variable (R κ : Type) [Field R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j,earlierWeights κ n B i j=0 ↔ laterWeights κ n B i j=0)
variable (hf : ∀ I,Independent (laterWeights κ n B) I → Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))
variable (hs : ∀ I,Independent (laterWeights κ n B) I → FreezingLattice.Saturated (LinearMap.range (GlobalExchangeSmooth.selectedMap κ n B I)))
variable {G : Scheme → Type*} [∀ X,AddCommGroup (G X)]
variable (T : SchemeGZeroInput.Theory G) (K : SchemeGZeroInput.Koszul T)
variable (ST : SchemeGZeroInput.SplitAffineTorus T) (L : SchemeGZeroInput.Localization T)
variable (SC : SmoothCartanInput.Standard)

include hpos hneg hsupport hf hs K ST L in
theorem coherent_generated : Function.Surjective (fun z : ℤ => z •
    CoherentUnit.classOf (Global R κ n B)) := by
  intro a
  obtain ⟨z,hz⟩ := (OriginalGZeroFiltration.global_unit_bijective R κ n B hpos hneg hsupport hf hs T K ST L).2
    ((T.affine (Global R κ n B)).symm a)
  refine ⟨z,?_⟩
  have h := congrArg (T.affine (Global R κ n B)) hz
  change T.affine (Global R κ n B) (z • T.unit (Spec (CommRingCat.of (Global R κ n B))))=
    T.affine (Global R κ n B) ((T.affine (Global R κ n B)).symm a) at h
  simpa only [map_zsmul,T.affine_unit,AddEquiv.apply_symm_apply] using h

variable (F : Type) [Field F] [Algebra (Global R κ n B) F]

include hpos hneg hsupport hf hs K ST L SC in
theorem rank_bijective : Function.Bijective (ProjectiveFieldRank.rankMap (Global R κ n B) F) := by
  letI := GlobalExchangeSmooth.global_smooth_saturated R κ n B hpos hneg hsupport hf hs
  exact RankFromCartan.rank_bijective (Global R κ n B) F (SC.bijective R (Global R κ n B)).1
    (coherent_generated R κ n B hpos hneg hsupport hf hs T K ST L)

def rankEquiv : ProjectiveClasses.Completion (Global R κ n B) ≃+ ℤ :=
  AddEquiv.ofBijective (ProjectiveFieldRank.rankMap (Global R κ n B) F)
    (rank_bijective R κ n B hpos hneg hsupport hf hs T K ST L SC F)

include hpos hneg hsupport hf hs K ST L SC F in
theorem stably_free (Q : ActualProjectiveSplitting.Bundle (Global R κ n B)) :
    ActualStableCancellation.StablyFree (Global R κ n B) Q :=
  ActualKZeroStability.stablyFree (Global R κ n B) F
    (rank_bijective R κ n B hpos hneg hsupport hf hs T K ST L SC F).1 Q

#print axioms coherent_generated
#print axioms rank_bijective
#print axioms rankEquiv
#print axioms stably_free
end Verification.OriginalKZero
