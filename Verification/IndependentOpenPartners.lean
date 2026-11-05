/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.IndependentOpenCoordinates
import Verification.ActualOpenPartners

/-!
# Independent Open Partners

Relabeling and localization of the global open chart preserve every
selected mutated generator before its explicit negative-unit rescaling.
-/
noncomputable section
namespace Verification.IndependentOpenPartners
open MvPolynomial Verification.FrozenAcyclicCover Verification.IndependentChartIndex
open Verification.IndependentBasicOpen Verification.IndependentOpenCoordinates
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ) (I : Finset (Fin n))
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)

def selectedPartner (i : Selected n I) : BasicOpen R κ n I B :=
  algebraMap (Global R κ n B) _ (mutated R κ n B i.val)

theorem quotientEquiv_partner (i : Selected n I) :
    IndependentChartPresentation.quotientEquiv R κ n I B
      (Ideal.Quotient.mk _ (X (Sum.inl i.val)))=
    (Ideal.Quotient.mk _ (X (Sum.inl i)) : IndependentChartPresentation.NewPresentation R κ n I B) := by
  change Ideal.Quotient.mk _ (ExchangeRelabel.polynomialEquiv R (originals κ n I) (partners n I) (X (Sum.inl i.val)))=_
  rw [ExchangeRelabel.polynomialEquiv_X]
  have hi : partners n I (Sum.inl i.val)=Sum.inl i := by
    apply (partners n I).symm.injective
    rw [Equiv.symm_apply_apply]
    rfl
  rw [hi]

theorem presentation_openEquiv_partner (i : Selected n I) :
    IndependentChartPresentation.openEquiv R κ n I B
      (algebraMap (PolynomialPresentation R κ n B)
        (Localization (IndependentChartPresentation.complementMonoid R κ n I B))
        (Ideal.Quotient.mk _ (X (Sum.inl i.val))))=
    ActualOpenPartners.globalPartner R (Selected n I) (Other n I ⊕ κ) (Other n I) Sum.inl (matrix κ n I B) i := by
  have hh := IsLocalization.algEquivOfAlgEquiv_eq
    (S := Localization (IndependentChartPresentation.complementMonoid R κ n I B))
    (Q := Localization (FrozenOpenChart.complementMonoid R (Selected n I) (Other n I ⊕ κ) (Other n I) Sum.inl (matrix κ n I B)))
    (h := IndependentChartPresentation.quotientEquiv R κ n I B)
    (IndependentChartPresentation.map_complementMonoid R κ n I B)
    (Ideal.Quotient.mk _ (X (Sum.inl i.val)))
  rw [quotientEquiv_partner] at hh
  exact hh

theorem chartEquiv_partner (i : Selected n I) :
    chartEquiv R κ n I B (selectedPartner R κ n I B i)=
      ActualOpenPartners.globalPartner R (Selected n I) (Other n I ⊕ κ) (Other n I) Sum.inl (matrix κ n I B) i := by
  change IndependentChartPresentation.openEquiv R κ n I B
    (directEquiv R κ n I B (algebraMap (Global R κ n B) (BasicOpen R κ n I B)
      (algebraMap (PolynomialPresentation R κ n B) (Global R κ n B)
        (Ideal.Quotient.mk _ (X (Sum.inl i.val))))))=_
  rw [← IsScalarTower.algebraMap_apply,AlgEquiv.commutes,presentation_openEquiv_partner]

#print axioms selectedPartner
#print axioms quotientEquiv_partner
#print axioms presentation_openEquiv_partner
#print axioms chartEquiv_partner
end Verification.IndependentOpenPartners
