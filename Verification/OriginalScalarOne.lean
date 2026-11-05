/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarGlobalDomain
import Verification.IndependentChartPresentation

/-!
# Original Scalar One

The original exchange ring is the unit-scalar specialization of the
actual scalar exchange presentation, including its frozen localization.
Consequently the proved Laurent embedding gives the original ring's
integrality under AS, without a new domain hypothesis.
-/
noncomputable section
namespace Verification.OriginalScalarOne
open MvPolynomial Verification.ActualStratum Verification.StratumPresentation
open Verification.FrozenAcyclicCover
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)

theorem exchangeFamily_eq : ScalarFrozenGlobal.exchangeFamily R κ n B (fun _ => 1) (fun _ => 1)=
    exchangePolynomial R (Fin n) κ Empty B := by
  funext i
  cases i with
  | inl i => simp [ScalarFrozenGlobal.exchangeFamily,ScalarFrozenGlobal.scalarExchange,exchangePolynomial]
  | inr t => exact t.elim

def quotientEquiv : PolynomialPresentation R κ n B ≃ₐ[R]
    ScalarFrozenGlobal.Presentation R κ n B (fun _ => 1) (fun _ => 1) :=
  Ideal.quotientEquivAlgOfEq R (congrArg
    (exchangeIdeal (initialPolynomial R (Fin n) κ Empty (noMutable κ)))
      (exchangeFamily_eq R κ n B)).symm

theorem quotientEquiv_original (a : Fin n ⊕ κ) :
    quotientEquiv R κ n B (FrozenOpenChart.original R (Fin n) κ Empty (noMutable κ) B a)=
      ScalarFrozenGlobal.original R κ n B (fun _ => 1) (fun _ => 1) a := rfl

theorem map_frozenMonoid :
    (FrozenOpenChart.frozenMonoid R (Fin n) κ Empty (noMutable κ) B).map
      (quotientEquiv R κ n B).toMonoidHom=
    ScalarFrozenGlobal.frozenMonoid R κ n B (fun _ => 1) (fun _ => 1) := by
  unfold FrozenOpenChart.frozenMonoid ScalarFrozenGlobal.frozenMonoid
  rw [IndependentChartPresentation.map_generated]
  apply congrArg Submonoid.closure
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨a.val,(quotientEquiv_original R κ n B (Sum.inr a.val)).symm⟩
  · rintro ⟨a,rfl⟩
    refine ⟨⟨a,?_⟩,quotientEquiv_original R κ n B (Sum.inr a)⟩
    rintro ⟨t,_⟩
    exact t.elim

def globalEquiv : Global R κ n B ≃ₐ[R]
    ScalarFrozenGlobal.Global R κ n B (fun _ => 1) (fun _ => 1) :=
  IsLocalization.algEquivOfAlgEquiv (Global R κ n B)
    (ScalarFrozenGlobal.Global R κ n B (fun _ => 1) (fun _ => 1))
    (quotientEquiv R κ n B) (map_frozenMonoid R κ n B)

variable [IsDomain R]
variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat=0)
variable (hsupport : ∀ i j,earlierWeights κ n B i j=0 ↔ laterWeights κ n B i j=0)
variable (hall : ∀ I : Finset (Fin n),ExchangeOpenCover.Independent (laterWeights κ n B) I →
  AnticliqueSubcolumns.AS (fun a i => B a (Sum.inl i)) I)

include hpos hneg hsupport hall in
theorem global_domain : IsDomain (Global R κ n B) := by
  letI := ScalarGlobalDomain.global_domain R κ n B (fun _ => 1) (fun _ => 1)
    hpos hneg hsupport hall
  exact Function.Injective.isDomain (globalEquiv R κ n B).toRingHom
    (globalEquiv R κ n B).injective

#print axioms exchangeFamily_eq
#print axioms quotientEquiv
#print axioms quotientEquiv_original
#print axioms map_frozenMonoid
#print axioms globalEquiv
#print axioms global_domain
end Verification.OriginalScalarOne
