/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarGlobalNonzerodivisors
import Verification.ScalarInitialTorus

/-!
# Scalar Global Domain

The actual scalar global exchange ring embeds into its initial Laurent
ring. Over an integral coefficient ring it is therefore itself integral;
no global-domain hypothesis is used in the local regularity argument.
-/
noncomputable section
namespace Verification.ScalarGlobalDomain
open Verification.ScalarFrozenGlobal Verification.ScalarIndependentBasicOpen
open Verification.FrozenAcyclicCover (earlierWeights laterWeights)
open Verification.ExchangeOpenCover
open scoped BigOperators
variable (R κ : Type) [CommRing R] [Nontrivial R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (a b : Fin n → Rˣ)
variable (hpos : ∀ r i : Fin n, ¬ r < i → (B (Sum.inl r) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ r i : Fin n, ¬ i < r → (-B (Sum.inl r) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hall : ∀ I : Finset (Fin n), Independent (laterWeights κ n B) I →
  AnticliqueSubcolumns.AS (fun q j => B q (Sum.inl j)) I)
include hpos hneg hsupport hall

theorem initial_product_regular : IsSMulRegular (Global R κ n B a b) (chartValue R κ n ∅ B a b) := by
  classical
  change IsSMulRegular (Global R κ n B a b) (∏ i ∈ (∅ : Finset (Fin n))ᶜ, initial R κ n B a b (Sum.inl i))
  apply Finset.prod_induction _ (fun z => IsSMulRegular (Global R κ n B a b) z)
  · exact fun _ _ ha hb => ha.mul hb
  · exact (isUnit_one : IsUnit (1 : Global R κ n B a b)).isSMulRegular _
  · intro i _
    exact ScalarGlobalNonzerodivisors.coordinate_regular R κ n B a b hpos hneg hsupport hall i

theorem initial_localization_injective : Function.Injective
    (algebraMap (Global R κ n B a b) (BasicOpen R κ n ∅ B a b)) := by
  apply IsLocalization.injective (M := Submonoid.powers (chartValue R κ n ∅ B a b))
    (BasicOpen R κ n ∅ B a b)
  apply Submonoid.powers_le.mpr
  rw [mem_nonZeroDivisors_iff]
  intro z hz
  apply (initial_product_regular R κ n B a b hpos hneg hsupport hall).eq_zero_of_smul_eq_zero
  simpa only [smul_eq_mul,mul_comm] using hz

omit hpos hneg hsupport hall in
def laurentEmbedding : Global R κ n B a b →ₐ[R]
    OriginalTorus.Torus R (IndependentChartIndex.Other n ∅ ⊕ κ) :=
  (ScalarInitialTorus.initialTorusEquiv R κ n B a b).toAlgHom.comp
    (IsScalarTower.toAlgHom R (Global R κ n B a b) (BasicOpen R κ n ∅ B a b))

theorem laurentEmbedding_injective : Function.Injective (laurentEmbedding R κ n B a b) :=
  (ScalarInitialTorus.initialTorusEquiv R κ n B a b).injective.comp
    (initial_localization_injective R κ n B a b hpos hneg hsupport hall)

theorem global_domain [IsDomain R] : IsDomain (Global R κ n B a b) :=
  Function.Injective.isDomain (laurentEmbedding R κ n B a b).toRingHom
    (laurentEmbedding_injective R κ n B a b hpos hneg hsupport hall)

#print axioms initial_product_regular
#print axioms initial_localization_injective
#print axioms laurentEmbedding
#print axioms laurentEmbedding_injective
#print axioms global_domain
end Verification.ScalarGlobalDomain
