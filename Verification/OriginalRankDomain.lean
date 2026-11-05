/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalRankNonzerodivisors
import Verification.OriginalInitialTorus

/-!
# Original Rank Domain

The actual full-rank exchange algebra embeds into its actual initial
Laurent ring. Over an integral base it is therefore integral, without
saturation, split fibers, or the tame characteristic restriction.
-/
noncomputable section
namespace Verification.OriginalRankDomain
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
open Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.ExchangeOpenCover Verification.IndependentBasicOpen
open scoped BigOperators
variable (R κ : Type) [CommRing R] [Nontrivial R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hf : ∀ I, Independent (laterWeights κ n B) I →
  Function.Injective (GlobalExchangeSmooth.selectedMap κ n B I))

include hpos hneg hsupport hf in
theorem initial_product_regular : IsSMulRegular (Global R κ n B) (chartValue R κ n ∅ B) := by
  classical
  change IsSMulRegular (Global R κ n B) (∏ i ∈ (∅ : Finset (Fin n))ᶜ, initial R κ n B (Sum.inl i))
  apply Finset.prod_induction _ (fun z => IsSMulRegular (Global R κ n B) z)
  · exact fun _ _ ha hb => ha.mul hb
  · exact (isUnit_one : IsUnit (1 : Global R κ n B)).isSMulRegular _
  · intro i _
    exact OriginalRankNonzerodivisors.coordinate_regular R κ n B hpos hneg hsupport hf i

include hpos hneg hsupport hf in
theorem initial_localization_injective : Function.Injective
    (algebraMap (Global R κ n B) (BasicOpen R κ n ∅ B)) := by
  apply IsLocalization.injective (M := Submonoid.powers (chartValue R κ n ∅ B))
    (BasicOpen R κ n ∅ B)
  apply Submonoid.powers_le.mpr
  rw [mem_nonZeroDivisors_iff]
  intro z hz
  apply (initial_product_regular R κ n B hpos hneg hsupport hf).eq_zero_of_smul_eq_zero
  simpa only [smul_eq_mul, mul_comm] using hz

include hpos hneg hsupport hf in
theorem global_domain [IsDomain R] : IsDomain (Global R κ n B) := by
  let e := OriginalInitialTorus.initialTorusEquiv R κ n B
  letI : IsDomain (BasicOpen R κ n ∅ B) := Function.Injective.isDomain e.toRingHom e.injective
  exact Function.Injective.isDomain
    (algebraMap (Global R κ n B) (BasicOpen R κ n ∅ B))
    (initial_localization_injective R κ n B hpos hneg hsupport hf)

#print axioms initial_product_regular
#print axioms initial_localization_injective
#print axioms global_domain
end Verification.OriginalRankDomain
