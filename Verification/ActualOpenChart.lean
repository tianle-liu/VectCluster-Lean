/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualStratum
import Verification.PartialOriginalLocalization
import Verification.OpenChartPresentation
import Verification.LocallyClosedAlgebra
import Verification.LocalExchangeParameters

/-!
# Actual Open Chart

The actual global open exchange chart, with no selected x-coordinate
killed, is the literal local model. All original exchange monomials are
transported; complementary partners are eliminated and selected partners
are rescaled by their explicitly constructed negative-monomial units.
-/

noncomputable section
universe u
namespace Verification.ActualOpenChart
open MvPolynomial Verification.ActualStratum Verification.StratumPresentation
open Verification.PartialOriginalLocalization
open scoped BigOperators
variable (R ι κ τ : Type u) [CommRing R] [Fintype ι] [Fintype κ]

abbrev Original := OriginalPolynomial R ι κ
abbrev LocalBase := OpenOriginal R ι κ
abbrev Coefficients := PartialOriginalLocalization.Torus R κ

def localizedInitial (j : τ → κ) (v : ι ⊕ τ) : LocalBase R ι κ :=
  algebraMap (Original R ι κ) (LocalBase R ι κ) (initialPolynomial R ι κ τ j v)

def localizedExchange (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ) (v : ι ⊕ τ) : LocalBase R ι κ :=
  algebraMap (Original R ι κ) (LocalBase R ι κ) (exchangePolynomial R ι κ τ B v)

def negativeUnits (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ) (i : ι) : (Coefficients R κ)ˣ :=
  ExchangeCharacters.negativeUnit Finset.univ (fun k => B (Sum.inr k) (Sum.inl i))
    (fun k => Finsupp.single k 1)

def column (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ) (i : ι) : κ →₀ ℤ :=
  ExchangeCharacters.column Finset.univ (fun k => B (Sum.inr k) (Sum.inl i))
    (fun k => Finsupp.single k 1)

def characters (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ) (i : ι) : (Coefficients R κ)ˣ :=
  (MonoidAlgebra.of R (Multiplicative (κ →₀ ℤ))).toHomUnits
    (Multiplicative.ofAdd (column ι κ τ B i))

omit [Fintype ι] [Fintype κ] in
theorem originalEquiv_generator (p : Original R ι κ) :
    openOriginalEquiv R ι κ (algebraMap (Original R ι κ) (LocalBase R ι κ) p) =
      PartialOriginalLocalization.polynomialMap R ι κ p :=
  IsLocalization.lift_eq (PartialOriginalLocalization.polynomialMap_units R ι κ) p

omit [Fintype ι] [Fintype κ] in
theorem localizedInitial_unit (j : τ → κ) (t : τ) :
    localizedInitial R ι κ τ j (Sum.inr t) = (coordinateUnits R ι κ (j t) : LocalBase R ι κ) :=
  (coordinate_unit R ι κ (j t)).unit_spec.symm

omit [Fintype ι] [Fintype κ] in
theorem localizedInitial_free (j : τ → κ) (i : ι) :
    openOriginalEquiv R ι κ (localizedInitial R ι κ τ j (Sum.inl i)) = X i :=
  toTarget_coordinate R ι κ (Sum.inl i)

theorem localizedExchange_free (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
    (hB : ∀ a i : ι, B (Sum.inl a) (Sum.inl i) = 0) (i : ι) :
    openOriginalEquiv R ι κ (localizedExchange R ι κ τ B (Sum.inl i)) =
      C ((negativeUnits R ι κ τ B i : Coefficients R κ) * (1 + (characters R ι κ τ B i : Coefficients R κ))) := by
  rw [localizedExchange, originalEquiv_generator]
  have hE : PartialOriginalLocalization.polynomialMap R ι κ (exchangePolynomial R ι κ τ B (Sum.inl i)) =
      C (ExchangeCharacters.exchange (R := R) Finset.univ
        (fun k => B (Sum.inr k) (Sum.inl i)) (fun k => (Finsupp.single k 1 : κ →₀ ℤ))) := by
    simp only [exchangePolynomial, map_add, map_prod, map_pow,
      PartialOriginalLocalization.polynomialMap, aeval_X, Fintype.prod_sum_type,
      Sum.elim_inl, Sum.elim_inr, hB, Int.toNat_zero, neg_zero, pow_zero,
      Finset.prod_const_one, one_mul]
    simp only [ExchangeCharacters.exchange, map_add, map_prod, map_pow,
      ExchangeCharacters.monomial, Verification.OriginalTorus.torusCoordinate]
  rw [hE, ExchangeCharacters.exchange_factor]
  simp only [map_neg, map_one, sub_neg_eq_add]
  change C ((negativeUnits R ι κ τ B i : Coefficients R κ) *
    ((characters R ι κ τ B i : Coefficients R κ) + 1)) = _
  rw [add_comm]

def localizedChartEquiv (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
    (hB : ∀ a i : ι, B (Sum.inl a) (Sum.inl i) = 0) :
    (MvPolynomial (ι ⊕ τ) (LocalBase R ι κ) ⧸
      exchangeIdeal (localizedInitial R ι κ τ j) (localizedExchange R ι κ τ B)) ≃ₐ[R]
      LocalExchangeSmooth.LocalAlgebra (characters R ι κ τ B) :=
  OpenChartPresentation.preparedOpenEquiv (openOriginalEquiv R ι κ)
    (localizedInitial R ι κ τ j) (localizedExchange R ι κ τ B)
    (fun t => coordinateUnits R ι κ (j t)) (negativeUnits R ι κ τ B) (characters R ι κ τ B)
    (localizedInitial_unit R ι κ τ j) (localizedInitial_free R ι κ τ j)
    (localizedExchange_free R ι κ τ B hB)

abbrev GlobalOpen (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ) :=
  Localization ((PolynomialLocalization.coefficientMonoid (α := ι ⊕ τ) (coordinateMonoid R ι κ)).map
    (Ideal.Quotient.mk (exchangeIdeal (initialPolynomial R ι κ τ j) (exchangePolynomial R ι κ τ B))))

attribute [local instance] MvPolynomial.algebraMvPolynomial

def globalToLocalized (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ) :
    GlobalOpen R ι κ τ j B ≃ₐ[Original R ι κ]
      (MvPolynomial (ι ⊕ τ) (LocalBase R ι κ) ⧸
        exchangeIdeal (localizedInitial R ι κ τ j) (localizedExchange R ι κ τ B)) :=
  AlgEquiv.ofRingEquiv (f := PolynomialLocalization.exchangeOpenLocusEquiv (coordinateMonoid R ι κ)
    (initialPolynomial R ι κ τ j) (exchangePolynomial R ι κ τ B)) (fun p => by
      simpa only [map_C] using LocallyClosedAlgebra.exchangeOpenLocusEquiv_generator (coordinateMonoid R ι κ)
        (initialPolynomial R ι κ τ j) (exchangePolynomial R ι κ τ B) (C p))

def globalOpenEquiv (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
    (hB : ∀ a i : ι, B (Sum.inl a) (Sum.inl i) = 0) :
    GlobalOpen R ι κ τ j B ≃ₐ[R] LocalExchangeSmooth.LocalAlgebra (characters R ι κ τ B) :=
  ((globalToLocalized R ι κ τ j B).restrictScalars R).trans (localizedChartEquiv R ι κ τ j B hB)

def globalCoordinate (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ) (i : ι) : GlobalOpen R ι κ τ j B :=
  algebraMap (Original R ι κ) (GlobalOpen R ι κ τ j B) (X (Sum.inl i))

theorem globalOpenEquiv_coordinate (j : τ → κ) (B : (ι ⊕ κ) → (ι ⊕ τ) → ℤ)
    (hB : ∀ a i : ι, B (Sum.inl a) (Sum.inl i) = 0) (i : ι) :
    globalOpenEquiv R ι κ τ j B hB (globalCoordinate R ι κ τ j B i) =
      LocalExchangeSmooth.x (characters R ι κ τ B) i := by
  change localizedChartEquiv R ι κ τ j B hB
    ((globalToLocalized R ι κ τ j B) (algebraMap (Original R ι κ) _ (X (Sum.inl i)))) = _
  rw [AlgEquiv.commutes]
  exact OpenChartPresentation.preparedOpenEquiv_original (openOriginalEquiv R ι κ)
    (localizedInitial R ι κ τ j) (localizedExchange R ι κ τ B)
    (fun t => coordinateUnits R ι κ (j t)) (negativeUnits R ι κ τ B) (characters R ι κ τ B)
    (localizedInitial_unit R ι κ τ j) (localizedInitial_free R ι κ τ j)
    (localizedExchange_free R ι κ τ B hB) i

#print axioms Original
#print axioms LocalBase
#print axioms Coefficients
#print axioms localizedInitial
#print axioms localizedExchange
#print axioms negativeUnits
#print axioms column
#print axioms characters
#print axioms originalEquiv_generator
#print axioms localizedInitial_unit
#print axioms localizedInitial_free
#print axioms localizedExchange_free
#print axioms localizedChartEquiv
#print axioms GlobalOpen
#print axioms globalToLocalized
#print axioms globalOpenEquiv
#print axioms globalCoordinate
#print axioms globalOpenEquiv_coordinate
end Verification.ActualOpenChart
