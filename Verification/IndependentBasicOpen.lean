/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.IndependentChartPresentation
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Independent Basic Open

The principal open of the fixed frozen presentation at the product of
the complementary mutable coordinates is exactly the directly localized
and relabeled chart.
-/
noncomputable section
namespace Verification.IndependentBasicOpen
open Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.ExchangeOpenCover
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ) (I : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)
attribute [local instance] MvPolynomial.algebraMvPolynomial

abbrev chartValue := chartElement (fun i => initial R κ n B (Sum.inl i)) I

abbrev BasicOpen := Localization.Away (chartValue R κ n I B)

theorem frozen_le_complement :
    FrozenOpenChart.frozenMonoid R (Fin n) κ Empty (noMutable κ) B ≤
      IndependentChartPresentation.complementMonoid R κ n I B := by
  apply Submonoid.closure_le.mpr
  rintro _ ⟨k, rfl⟩
  apply Submonoid.subset_closure
  exact ⟨Sum.inr k.1, rfl⟩

theorem chartValue_mem : chartValue R κ n I B ∈
    (IndependentChartPresentation.complementMonoid R κ n I B).map
      (algebraMap (PolynomialPresentation R κ n B) (Global R κ n B)) := by
  classical
  apply Submonoid.prod_mem
  intro i hi
  refine ⟨FrozenOpenChart.original R (Fin n) κ Empty (noMutable κ) B (Sum.inl i), ?_, rfl⟩
  apply Submonoid.subset_closure
  exact ⟨Sum.inl ⟨i, Finset.mem_compl.mp hi⟩, rfl⟩

theorem complement_units (a : Other n I ⊕ κ) : IsUnit
    (algebraMap (Global R κ n B) (BasicOpen R κ n I B)
      (initial R κ n B (IndependentChartPresentation.complementEmbedding κ n I a))) := by
  classical
  cases a with
  | inl i =>
      exact IsLocalization.Away.isUnit_of_dvd (chartValue R κ n I B)
        (Finset.dvd_prod_of_mem _ (Finset.mem_compl.mpr i.2))
  | inr k => exact (frozen_unit R κ n B k).map _

theorem away_isLocalization : IsLocalization
    ((IndependentChartPresentation.complementMonoid R κ n I B).map
      (algebraMap (PolynomialPresentation R κ n B) (Global R κ n B)))
    (BasicOpen R κ n I B) := by
  apply IsLocalization.of_le (Submonoid.powers (chartValue R κ n I B))
  · exact Submonoid.powers_le.mpr (chartValue_mem R κ n I B)
  · rintro _ ⟨a, ha, rfl⟩
    apply SplitExchangeChart.units_on_closure
      ((algebraMap (Global R κ n B) (BasicOpen R κ n I B)).comp
        (algebraMap (PolynomialPresentation R κ n B) (Global R κ n B)))
      (fun a => FrozenOpenChart.original R (Fin n) κ Empty (noMutable κ) B
        (IndependentChartPresentation.complementEmbedding κ n I a)) _ ⟨a, ha⟩
    exact complement_units R κ n I B

def toDirect : Global R κ n B →ₐ[PolynomialPresentation R κ n B]
    Localization (IndependentChartPresentation.complementMonoid R κ n I B) :=
  IsLocalization.liftAlgHom
    (M := FrozenOpenChart.frozenMonoid R (Fin n) κ Empty (noMutable κ) B)
    (f := Algebra.ofId (PolynomialPresentation R κ n B)
      (Localization (IndependentChartPresentation.complementMonoid R κ n I B)))
    (fun m => IsLocalization.map_units _
      (⟨(m : PolynomialPresentation R κ n B), frozen_le_complement R κ n I B m.2⟩ :
        IndependentChartPresentation.complementMonoid R κ n I B))

def directEquiv : BasicOpen R κ n I B ≃ₐ[PolynomialPresentation R κ n B]
    Localization (IndependentChartPresentation.complementMonoid R κ n I B) := by
  letI := away_isLocalization R κ n I B
  letI : SMul (PolynomialPresentation R κ n B)
      (Localization (IndependentChartPresentation.complementMonoid R κ n I B)) :=
    (inferInstance : Algebra (PolynomialPresentation R κ n B)
      (Localization (IndependentChartPresentation.complementMonoid R κ n I B))).toSMul
  letI : Algebra (Global R κ n B)
      (Localization (IndependentChartPresentation.complementMonoid R κ n I B)) :=
    (toDirect R κ n I B).toRingHom.toAlgebra
  letI : SMul (Global R κ n B)
      (Localization (IndependentChartPresentation.complementMonoid R κ n I B)) :=
    (toDirect R κ n I B).toRingHom.toAlgebra.toSMul
  letI : IsScalarTower (PolynomialPresentation R κ n B) (Global R κ n B)
      (Localization (IndependentChartPresentation.complementMonoid R κ n I B)) :=
    IsScalarTower.of_algebraMap_eq (fun a => (toDirect R κ n I B).commutes a |>.symm)
  letI : IsLocalization
      ((IndependentChartPresentation.complementMonoid R κ n I B).map
        (algebraMap (PolynomialPresentation R κ n B) (Global R κ n B)))
      (Localization (IndependentChartPresentation.complementMonoid R κ n I B)) :=
    IsLocalization.isLocalization_of_submonoid_le (Global R κ n B) _ _ _ (frozen_le_complement R κ n I B)
  exact (IsLocalization.algEquiv
    ((IndependentChartPresentation.complementMonoid R κ n I B).map
      (algebraMap (PolynomialPresentation R κ n B) (Global R κ n B)))
    (BasicOpen R κ n I B)
    (Localization (IndependentChartPresentation.complementMonoid R κ n I B))).restrictScalars
      (PolynomialPresentation R κ n B)

def chartEquiv : BasicOpen R κ n I B ≃ₐ[R]
    ActualOpenChart.GlobalOpen R (Selected n I) (Other n I ⊕ κ) (Other n I)
      Sum.inl (matrix κ n I B) :=
  ((directEquiv R κ n I B).restrictScalars R).trans
    (IndependentChartPresentation.openEquiv R κ n I B)

#print axioms chartValue
#print axioms BasicOpen
#print axioms frozen_le_complement
#print axioms chartValue_mem
#print axioms complement_units
#print axioms away_isLocalization
#print axioms toDirect
#print axioms directEquiv
#print axioms chartEquiv
end Verification.IndependentBasicOpen
