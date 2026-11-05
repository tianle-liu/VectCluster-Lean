/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OriginalDivisorGeometry
import Verification.ScalarInitialTorus

/-!
# Original Initial Torus

The initial principal open in the original exchange algebra is a split
torus on all mutable and frozen coordinates. The scalar-one transport is
tracked on the actual defining product, so this is an isomorphism of the
literal principal localization, not an abstract birational presentation.
-/
noncomputable section
namespace Verification.OriginalInitialTorus
open Verification.FrozenAcyclicCover Verification.ExchangeOpenCover
open Verification.IndependentChartIndex
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
open scoped BigOperators

variable (I : Finset (Fin n))

theorem map_chartValue : OriginalScalarOne.globalEquiv R κ n B
    (IndependentBasicOpen.chartValue R κ n I B) =
      ScalarIndependentBasicOpen.chartValue R κ n I B (fun _ => 1) (fun _ => 1) := by
  classical
  simp only [IndependentBasicOpen.chartValue, ScalarIndependentBasicOpen.chartValue,
    chartElement, map_prod, OriginalScalarNormalization.one_initial]

theorem map_chartPowers :
    (Submonoid.powers (IndependentBasicOpen.chartValue R κ n I B)).map
      (OriginalScalarOne.globalEquiv R κ n B).toMonoidHom =
        Submonoid.powers (ScalarIndependentBasicOpen.chartValue R κ n I B (fun _ => 1) (fun _ => 1)) := by
  rw [Submonoid.map_powers]
  change Submonoid.powers (OriginalScalarOne.globalEquiv R κ n B
    (IndependentBasicOpen.chartValue R κ n I B)) = _
  rw [map_chartValue]

def chartScalarEquiv : IndependentBasicOpen.BasicOpen R κ n I B ≃ₐ[R]
    ScalarIndependentBasicOpen.BasicOpen R κ n I B (fun _ => 1) (fun _ => 1) :=
  IsLocalization.algEquivOfAlgEquiv _ _ (OriginalScalarOne.globalEquiv R κ n B)
    (map_chartPowers R κ n B I)

def initialTorusEquiv : IndependentBasicOpen.BasicOpen R κ n ∅ B ≃ₐ[R]
    OriginalTorus.Torus R (Other n ∅ ⊕ κ) :=
  (chartScalarEquiv R κ n B ∅).trans
    (ScalarInitialTorus.initialTorusEquiv R κ n B (fun _ => 1) (fun _ => 1))

variable [IsDomain R]
variable (hpos : ∀ a i : Fin n, ¬a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
variable (hall : ∀ I : Finset (Fin n), Independent (laterWeights κ n B) I →
  AnticliqueSubcolumns.AS (fun a i => B a (Sum.inl i)) I)

include hpos hneg hsupport hall in
theorem coordinate_nonzero (i : Fin n) : initial R κ n B (Sum.inl i) ≠ 0 := by
  letI := OriginalScalarOne.global_domain R κ n B hpos hneg hsupport hall
  have hr := OriginalDivisorGeometry.coordinate_regular R κ n B hpos hneg hsupport hall i
  intro h
  have h10 : (1 : Global R κ n B) = 0 := hr (by
    change initial R κ n B (Sum.inl i) * 1 = initial R κ n B (Sum.inl i) * 0
    rw [h, zero_mul, zero_mul])
  exact one_ne_zero h10

include hpos hneg hsupport hall in
theorem chartValue_nonzero : IndependentBasicOpen.chartValue R κ n ∅ B ≠ 0 := by
  letI := OriginalScalarOne.global_domain R κ n B hpos hneg hsupport hall
  classical
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => coordinate_nonzero R κ n B hpos hneg hsupport hall i)

include hpos hneg hsupport hall in
theorem initialTorus_dense : Dense
    (PrimeSpectrum.basicOpen (IndependentBasicOpen.chartValue R κ n ∅ B) :
      Set (PrimeSpectrum (Global R κ n B))) := by
  letI := OriginalScalarOne.global_domain R κ n B hpos hneg hsupport hall
  apply (PrimeSpectrum.basicOpen (IndependentBasicOpen.chartValue R κ n ∅ B)).isOpen.dense
  exact ⟨⟨⊥, Ideal.bot_prime⟩, chartValue_nonzero R κ n B hpos hneg hsupport hall⟩

#print axioms map_chartValue
#print axioms map_chartPowers
#print axioms chartScalarEquiv
#print axioms initialTorusEquiv
#print axioms coordinate_nonzero
#print axioms chartValue_nonzero
#print axioms initialTorus_dense
end Verification.OriginalInitialTorus
