/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.OpenChartPresentation

/-!
# Open Chart Partners

Images of the retained exchange partners in the proved chart isomorphism.
The only rescaling is the previously explicit negative-monomial unit.
-/
noncomputable section
universe u
namespace Verification.OpenChartPartners
open MvPolynomial Verification.OpenChartPresentation
variable {R T L ι κ : Type u} [CommRing R] [CommRing T] [CommRing L]
  [Algebra R T] [Algebra R L]

theorem elimination_X (x g : (ι ⊕ κ) → L) (u : κ → Lˣ)
    (hu : ∀ k, x (Sum.inr k) = (u k : L)) (i : ι) :
    EliminationWithResidual.exchangeQuotientEquiv x g u hu
      (Ideal.Quotient.mk (StratumPresentation.exchangeIdeal x g) (X (Sum.inl i))) =
      Ideal.Quotient.mk (EliminationWithResidual.residualIdeal x g) (X i) := by
  dsimp only [EliminationWithResidual.exchangeQuotientEquiv, AlgEquiv.trans_apply]
  rw [Ideal.quotientEquivAlgOfEq_mk]
  change EliminationWithResidual.quotientRingEquiv (EliminationWithResidual.residualIdeal x g) u
    (fun k => g (Sum.inr k)) (Ideal.Quotient.mk _ (X (Sum.inl i))) = _
  rw [EliminationWithResidual.quotientRingEquiv_generator]
  simp [Elimination.substitute]

theorem rescale_X (a χ : ι → Tˣ) (i : ι) :
    RescaleExchange.quotientEquiv a χ (Ideal.Quotient.mk (RescaleExchange.rawRelations a χ) (X (Sum.inr i))) =
      algebraMap T (LocalExchangeSmooth.LocalAlgebra χ) (a i : T) * LocalExchangeSmooth.y χ i := by
  change Ideal.Quotient.mk _ (RescaleExchange.scaleHom a (X (Sum.inr i))) = _
  rw [RescaleExchange.scaleHom_X_right,map_mul]
  rfl

theorem preparedOpenEquiv_partner (E : L ≃ₐ[R] MvPolynomial ι T)
    (x g : (ι ⊕ κ) → L) (u : κ → Lˣ) (a χ : ι → Tˣ)
    (hu : ∀ k, x (Sum.inr k) = (u k : L))
    (hx : ∀ i, E (x (Sum.inl i)) = X i)
    (hg : ∀ i, E (g (Sum.inl i)) = C ((a i : T) * (1 + (χ i : T)))) (i : ι) :
    preparedOpenEquiv E x g u a χ hu hx hg
      (Ideal.Quotient.mk (StratumPresentation.exchangeIdeal x g) (X (Sum.inl i))) =
      algebraMap T (LocalExchangeSmooth.LocalAlgebra χ) (a i : T) * LocalExchangeSmooth.y χ i := by
  change residualEquiv E x g a χ hx hg
    (EliminationWithResidual.exchangeQuotientEquiv x g u hu
      (Ideal.Quotient.mk _ (X (Sum.inl i)))) = _
  rw [elimination_X]
  change RescaleExchange.quotientEquiv a χ (Ideal.Quotient.mk _ (flattenCoefficients E (X i))) = _
  rw [flattenCoefficients_X,rescale_X]

#print axioms elimination_X
#print axioms rescale_X
#print axioms preparedOpenEquiv_partner
end Verification.OpenChartPartners
