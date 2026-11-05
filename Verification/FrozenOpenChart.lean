/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualOpenChart
import Verification.NestedLocalization

/-!
# Frozen Open Chart

The global presentation with frozen original variables inverted has the
same open chart as the direct complement localization used in ActualOpenChart.
Here the frozen coordinates are exactly those outside the image of the
complementary mutable-variable map j.
-/
noncomputable section
universe u
namespace Verification.FrozenOpenChart
open MvPolynomial Verification.ActualStratum Verification.StratumPresentation
variable (R ι κ τ : Type u) [CommRing R] [Fintype ι] [Fintype κ]
variable (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)

abbrev Presentation := MvPolynomial (ι ⊕ τ) (OriginalPolynomial R ι κ) ⧸
  exchangeIdeal (initialPolynomial R ι κ τ j) (exchangePolynomial R ι κ τ B)

def original (v : ι ⊕ κ) : Presentation R ι κ τ j B :=
  Ideal.Quotient.mk _ (C (X v))

def complementMonoid : Submonoid (Presentation R ι κ τ j B) :=
  (PolynomialLocalization.coefficientMonoid (α := ι ⊕ τ)
    (PartialOriginalLocalization.coordinateMonoid R ι κ)).map (Ideal.Quotient.mk _)

def frozenMonoid : Submonoid (Presentation R ι κ τ j B) :=
  Submonoid.closure (Set.range (fun k : {k : κ // k ∉ Set.range j} =>
    original R ι κ τ j B (Sum.inr k.1)))

abbrev FrozenPresentation := Localization (frozenMonoid R ι κ τ j B)

abbrev OpenInFrozen := NestedLocalization.Iterated (frozenMonoid R ι κ τ j B)
  (complementMonoid R ι κ τ j B)

theorem frozen_le_complement : frozenMonoid R ι κ τ j B ≤ complementMonoid R ι κ τ j B := by
  apply Submonoid.closure_le.mpr
  rintro _ ⟨k, rfl⟩
  refine ⟨C (X (Sum.inr k.1)), ?_, rfl⟩
  refine ⟨X (Sum.inr k.1), ?_, rfl⟩
  exact Submonoid.subset_closure (Set.mem_range_self k.1)

def openEquiv : OpenInFrozen R ι κ τ j B ≃ₐ[Presentation R ι κ τ j B]
    ActualOpenChart.GlobalOpen R ι κ τ j B :=
  NestedLocalization.equiv (frozenMonoid R ι κ τ j B) (complementMonoid R ι κ τ j B)
    (frozen_le_complement R ι κ τ j B)

theorem openEquiv_original (v : ι ⊕ κ) :
    openEquiv R ι κ τ j B
      (algebraMap (Presentation R ι κ τ j B) (OpenInFrozen R ι κ τ j B)
        (original R ι κ τ j B v)) =
    algebraMap (Presentation R ι κ τ j B) (ActualOpenChart.GlobalOpen R ι κ τ j B)
      (original R ι κ τ j B v) := (openEquiv R ι κ τ j B).commutes _

#print axioms Presentation
#print axioms original
#print axioms complementMonoid
#print axioms frozenMonoid
#print axioms FrozenPresentation
#print axioms OpenInFrozen
#print axioms frozen_le_complement
#print axioms openEquiv
#print axioms openEquiv_original
end Verification.FrozenOpenChart
