/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarIndependentChartPresentation
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Scalar Independent Basic Open

The principal open of the fixed frozen presentation at the product of
the complementary mutable coordinates is exactly the directly localized
and relabeled chart.
-/
noncomputable section
namespace Verification.ScalarIndependentBasicOpen
open Verification.ScalarFrozenGlobal Verification.IndependentChartIndex
open Verification.ExchangeOpenCover
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ) (I : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (a b : Fin n → Rˣ)
attribute [local instance] MvPolynomial.algebraMvPolynomial

abbrev chartValue := chartElement (fun i => initial R κ n B a b (Sum.inl i)) I

abbrev BasicOpen := Localization.Away (chartValue R κ n I B a b)

theorem frozen_le_complement :
    frozenMonoid R κ n B a b ≤
      ScalarIndependentChartPresentation.complementMonoid R κ n I B a b := by
  apply Submonoid.closure_le.mpr
  rintro _ ⟨k, rfl⟩
  apply Submonoid.subset_closure
  exact ⟨Sum.inr k, rfl⟩

theorem chartValue_mem : chartValue R κ n I B a b ∈
    (ScalarIndependentChartPresentation.complementMonoid R κ n I B a b).map
      (algebraMap (Presentation R κ n B a b) (Global R κ n B a b)) := by
  classical
  apply Submonoid.prod_mem
  intro i hi
  refine ⟨original R κ n B a b (Sum.inl i), ?_, rfl⟩
  apply Submonoid.subset_closure
  exact ⟨Sum.inl ⟨i, Finset.mem_compl.mp hi⟩, rfl⟩

theorem complement_units (q : Other n I ⊕ κ) : IsUnit
    (algebraMap (Global R κ n B a b) (BasicOpen R κ n I B a b)
      (initial R κ n B a b (IndependentChartPresentation.complementEmbedding κ n I q))) := by
  classical
  cases q with
  | inl i =>
      exact IsLocalization.Away.isUnit_of_dvd (chartValue R κ n I B a b)
        (Finset.dvd_prod_of_mem _ (Finset.mem_compl.mpr i.2))
  | inr k => exact (frozen_unit R κ n B a b k).map _

theorem away_isLocalization : IsLocalization
    ((ScalarIndependentChartPresentation.complementMonoid R κ n I B a b).map
      (algebraMap (Presentation R κ n B a b) (Global R κ n B a b)))
    (BasicOpen R κ n I B a b) := by
  apply IsLocalization.of_le (Submonoid.powers (chartValue R κ n I B a b))
  · exact Submonoid.powers_le.mpr (chartValue_mem R κ n I B a b)
  · rintro _ ⟨z, hz, rfl⟩
    apply SplitExchangeChart.units_on_closure
      ((algebraMap (Global R κ n B a b) (BasicOpen R κ n I B a b)).comp
        (algebraMap (Presentation R κ n B a b) (Global R κ n B a b)))
      (fun q => original R κ n B a b
        (IndependentChartPresentation.complementEmbedding κ n I q)) _ ⟨z, hz⟩
    exact complement_units R κ n I B a b

def toDirect : Global R κ n B a b →ₐ[Presentation R κ n B a b]
    Localization (ScalarIndependentChartPresentation.complementMonoid R κ n I B a b) :=
  IsLocalization.liftAlgHom
    (M := frozenMonoid R κ n B a b)
    (f := Algebra.ofId (Presentation R κ n B a b)
      (Localization (ScalarIndependentChartPresentation.complementMonoid R κ n I B a b)))
    (fun m => IsLocalization.map_units _
      (⟨(m : Presentation R κ n B a b), frozen_le_complement R κ n I B a b m.2⟩ :
        ScalarIndependentChartPresentation.complementMonoid R κ n I B a b))

def directEquiv : BasicOpen R κ n I B a b ≃ₐ[Presentation R κ n B a b]
    Localization (ScalarIndependentChartPresentation.complementMonoid R κ n I B a b) := by
  letI := away_isLocalization R κ n I B a b
  letI : SMul (Presentation R κ n B a b)
      (Localization (ScalarIndependentChartPresentation.complementMonoid R κ n I B a b)) :=
    (inferInstance : Algebra (Presentation R κ n B a b)
      (Localization (ScalarIndependentChartPresentation.complementMonoid R κ n I B a b))).toSMul
  letI : Algebra (Global R κ n B a b)
      (Localization (ScalarIndependentChartPresentation.complementMonoid R κ n I B a b)) :=
    (toDirect R κ n I B a b).toRingHom.toAlgebra
  letI : SMul (Global R κ n B a b)
      (Localization (ScalarIndependentChartPresentation.complementMonoid R κ n I B a b)) :=
    (toDirect R κ n I B a b).toRingHom.toAlgebra.toSMul
  letI : IsScalarTower (Presentation R κ n B a b) (Global R κ n B a b)
      (Localization (ScalarIndependentChartPresentation.complementMonoid R κ n I B a b)) :=
    IsScalarTower.of_algebraMap_eq (fun z => (toDirect R κ n I B a b).commutes z |>.symm)
  letI : IsLocalization
      ((ScalarIndependentChartPresentation.complementMonoid R κ n I B a b).map
        (algebraMap (Presentation R κ n B a b) (Global R κ n B a b)))
      (Localization (ScalarIndependentChartPresentation.complementMonoid R κ n I B a b)) :=
    IsLocalization.isLocalization_of_submonoid_le (Global R κ n B a b) _ _ _ (frozen_le_complement R κ n I B a b)
  exact (IsLocalization.algEquiv
    ((ScalarIndependentChartPresentation.complementMonoid R κ n I B a b).map
      (algebraMap (Presentation R κ n B a b) (Global R κ n B a b)))
    (BasicOpen R κ n I B a b)
    (Localization (ScalarIndependentChartPresentation.complementMonoid R κ n I B a b))).restrictScalars
      (Presentation R κ n B a b)

def chartEquiv : BasicOpen R κ n I B a b ≃ₐ[R]
    ScalarActualOpenChart.GlobalOpen R (Selected n I) (Other n I ⊕ κ) (Other n I)
      (ScalarIndependentChartPresentation.newScalar R n I a)
      (ScalarIndependentChartPresentation.newScalar R n I b) Sum.inl (matrix κ n I B) :=
  ((directEquiv R κ n I B a b).restrictScalars R).trans
    (ScalarIndependentChartPresentation.openEquiv R κ n I B a b)

#print axioms chartValue
#print axioms BasicOpen
#print axioms frozen_le_complement
#print axioms chartValue_mem
#print axioms complement_units
#print axioms away_isLocalization
#print axioms toDirect
#print axioms directEquiv
#print axioms chartEquiv
end Verification.ScalarIndependentBasicOpen
