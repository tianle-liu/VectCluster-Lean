/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarExchangeRelabel
import Verification.ScalarCharacterLocalForm
import Verification.ActualOpenChart
import Verification.PartialOriginalLocalization
import Verification.OpenChartPresentation
import Verification.LocallyClosedAlgebra
import Verification.LocalExchangeParameters

/-!
# Scalar Actual Open Chart

The actual global open exchange chart, with no selected x-coordinate
killed, is the literal local model. All original exchange monomials are
transported; complementary partners are eliminated and selected partners
are rescaled by their explicitly constructed negative-monomial units.
-/

noncomputable section
universe u
namespace Verification.ScalarActualOpenChart
open MvPolynomial Verification.ActualStratum Verification.StratumPresentation
open Verification.PartialOriginalLocalization
open scoped BigOperators
variable (R ι κ τ : Type u) [CommRing R] [Fintype ι] [Fintype κ]
variable (a b : (ι ⊕ τ) → Rˣ)

abbrev Original := OriginalPolynomial R ι κ
abbrev LocalBase := OpenOriginal R ι κ
abbrev Coefficients := PartialOriginalLocalization.Torus R κ

def exchangePolynomial (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ) (v : ι ⊕ τ) : Original R ι κ :=
  ScalarExchangeRelabel.powerSum R (fun q => B q v) (a v) (b v)

def localizedExchange (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ) (v : ι ⊕ τ) : LocalBase R ι κ :=
  algebraMap (Original R ι κ) (LocalBase R ι κ) (exchangePolynomial R ι κ τ a b B v)

def negativeUnits (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ) (i : ι) : (Coefficients R κ)ˣ :=
  ScalarCharacterLocalForm.coefficientUnit Finset.univ (fun k => B (Sum.inr k) (Sum.inl i))
    (fun k => Finsupp.single k 1) (b (Sum.inl i))

def characters (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ) (i : ι) : (Coefficients R κ)ˣ :=
  ScalarCharacterLocalForm.characterUnit Finset.univ (fun k => B (Sum.inr k) (Sum.inl i))
    (fun k => Finsupp.single k 1) (a (Sum.inl i)) (b (Sum.inl i))

open Verification.ActualOpenChart (localizedInitial localizedInitial_unit localizedInitial_free originalEquiv_generator)

theorem localizedExchange_free (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
    (hB : ∀ a i : ι, B (Sum.inl a) (Sum.inl i) = 0) (i : ι) :
    openOriginalEquiv R ι κ (localizedExchange R ι κ τ a b B (Sum.inl i)) =
      C ((negativeUnits R ι κ τ b B i : Coefficients R κ) * (1 + (characters R ι κ τ a b B i : Coefficients R κ))) := by
  rw [localizedExchange, originalEquiv_generator]
  have hE : PartialOriginalLocalization.polynomialMap R ι κ
      (exchangePolynomial R ι κ τ a b B (Sum.inl i)) =
      C (ScalarExchangeCharacters.exchange (R := R) Finset.univ
        (fun k => B (Sum.inr k) (Sum.inl i)) (fun k => (Finsupp.single k 1 : κ →₀ ℤ))
          (a (Sum.inl i)) (b (Sum.inl i))) := by
    simp only [exchangePolynomial, ScalarExchangeRelabel.powerSum, map_add, map_mul, map_prod, map_pow,
      PartialOriginalLocalization.polynomialMap, aeval_C, aeval_X, Fintype.prod_sum_type,
      Sum.elim_inl, Sum.elim_inr, hB, Int.toNat_zero, neg_zero, pow_zero,
      Finset.prod_const_one, one_mul]
    simp only [ScalarExchangeCharacters.exchange, map_add, map_mul, map_prod, map_pow,
      ExchangeCharacters.monomial, Verification.OriginalTorus.torusCoordinate]
    rfl
  rw [hE, ScalarCharacterLocalForm.exchange_form]
  rfl

def localizedChartEquiv (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
    (hB : ∀ a i : ι, B (Sum.inl a) (Sum.inl i) = 0) :
    (MvPolynomial (ι ⊕ τ) (LocalBase R ι κ) ⧸
      exchangeIdeal (localizedInitial R ι κ τ j) (localizedExchange R ι κ τ a b B)) ≃ₐ[R]
      LocalExchangeSmooth.LocalAlgebra (characters R ι κ τ a b B) :=
  OpenChartPresentation.preparedOpenEquiv (openOriginalEquiv R ι κ)
    (localizedInitial R ι κ τ j) (localizedExchange R ι κ τ a b B)
    (fun t => coordinateUnits R ι κ (j t)) (negativeUnits R ι κ τ b B) (characters R ι κ τ a b B)
    (localizedInitial_unit R ι κ τ j) (localizedInitial_free R ι κ τ j)
    (localizedExchange_free R ι κ τ a b B hB)

abbrev GlobalOpen (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ) :=
  Localization ((PolynomialLocalization.coefficientMonoid (α := ι ⊕ τ) (coordinateMonoid R ι κ)).map
    (Ideal.Quotient.mk (exchangeIdeal (initialPolynomial R ι κ τ j) (exchangePolynomial R ι κ τ a b B))))

attribute [local instance] MvPolynomial.algebraMvPolynomial

def globalToLocalized (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ) :
    GlobalOpen R ι κ τ a b j B ≃ₐ[Original R ι κ]
      (MvPolynomial (ι ⊕ τ) (LocalBase R ι κ) ⧸
        exchangeIdeal (localizedInitial R ι κ τ j) (localizedExchange R ι κ τ a b B)) :=
  AlgEquiv.ofRingEquiv (f := PolynomialLocalization.exchangeOpenLocusEquiv (coordinateMonoid R ι κ)
    (initialPolynomial R ι κ τ j) (exchangePolynomial R ι κ τ a b B)) (fun p => by
      simpa only [map_C] using LocallyClosedAlgebra.exchangeOpenLocusEquiv_generator (coordinateMonoid R ι κ)
        (initialPolynomial R ι κ τ j) (exchangePolynomial R ι κ τ a b B) (C p))

def globalOpenEquiv (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
    (hB : ∀ a i : ι, B (Sum.inl a) (Sum.inl i) = 0) :
    GlobalOpen R ι κ τ a b j B ≃ₐ[R] LocalExchangeSmooth.LocalAlgebra (characters R ι κ τ a b B) :=
  ((globalToLocalized R ι κ τ a b j B).restrictScalars R).trans (localizedChartEquiv R ι κ τ a b j B hB)

def globalCoordinate (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ) (i : ι) : GlobalOpen R ι κ τ a b j B :=
  algebraMap (Original R ι κ) (GlobalOpen R ι κ τ a b j B) (X (Sum.inl i))

theorem globalOpenEquiv_coordinate (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
    (hB : ∀ a i : ι, B (Sum.inl a) (Sum.inl i) = 0) (i : ι) :
    globalOpenEquiv R ι κ τ a b j B hB (globalCoordinate R ι κ τ a b j B i) =
      LocalExchangeSmooth.x (characters R ι κ τ a b B) i := by
  change localizedChartEquiv R ι κ τ a b j B hB
    ((globalToLocalized R ι κ τ a b j B) (algebraMap (Original R ι κ) _ (X (Sum.inl i)))) = _
  rw [AlgEquiv.commutes]
  exact OpenChartPresentation.preparedOpenEquiv_original (openOriginalEquiv R ι κ)
    (localizedInitial R ι κ τ j) (localizedExchange R ι κ τ a b B)
    (fun t => coordinateUnits R ι κ (j t)) (negativeUnits R ι κ τ b B) (characters R ι κ τ a b B)
    (localizedInitial_unit R ι κ τ j) (localizedInitial_free R ι κ τ j)
    (localizedExchange_free R ι κ τ a b B hB) i

#print axioms Original
#print axioms LocalBase
#print axioms Coefficients
#print axioms exchangePolynomial
#print axioms localizedExchange
#print axioms negativeUnits
#print axioms characters
#print axioms localizedExchange_free
#print axioms localizedChartEquiv
#print axioms GlobalOpen
#print axioms globalToLocalized
#print axioms globalOpenEquiv
#print axioms globalCoordinate
#print axioms globalOpenEquiv_coordinate
end Verification.ScalarActualOpenChart
