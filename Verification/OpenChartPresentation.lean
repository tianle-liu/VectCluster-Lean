/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.EliminationWithResidual
import Verification.RescaleExchange
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Open Chart Presentation

The prepared open exchange presentation is the literal local exchange
quotient, by actual elimination, coefficient transport, and unit rescaling.
The hypotheses describe images of individual original coordinates and
exchange polynomials; no quotient or chart equivalence is assumed.
-/

noncomputable section
universe u
namespace Verification.OpenChartPresentation
open MvPolynomial
variable {R T L ι κ : Type u} [CommRing R] [CommRing T] [CommRing L]
  [Algebra R T] [Algebra R L]

def flatten (T ι : Type*) [CommRing T] :
    MvPolynomial ι (MvPolynomial ι T) ≃ₐ[T] MvPolynomial (ι ⊕ ι) T :=
  (sumAlgEquiv T ι ι).symm.trans (renameEquiv T (Equiv.sumComm ι ι))

theorem flatten_X (i : ι) : flatten T ι (X i) = X (Sum.inr i) := by
  change rename (Equiv.sumComm ι ι) (iterToSum T ι ι (X i)) = _
  simp

theorem flatten_C_X (i : ι) : flatten T ι (C (X i)) = X (Sum.inl i) := by
  change rename (Equiv.sumComm ι ι) (iterToSum T ι ι (C (X i))) = _
  simp

theorem flatten_C_C (t : T) : flatten T ι (C (C t)) = C t := by
  change rename (Equiv.sumComm ι ι) (iterToSum T ι ι (C (C t))) = _
  simp

def flattenCoefficients (E : L ≃ₐ[R] MvPolynomial ι T) :
    MvPolynomial ι L ≃ₐ[R] MvPolynomial (ι ⊕ ι) T :=
  (mapAlgEquiv ι E).trans ((flatten T ι).restrictScalars R)

theorem flattenCoefficients_X (E : L ≃ₐ[R] MvPolynomial ι T) (i : ι) :
    flattenCoefficients E (X i) = X (Sum.inr i) := by
  change flatten T ι (MvPolynomial.map E.toRingHom (X i)) = _
  rw [map_X, flatten_X]

theorem flattenCoefficients_C (E : L ≃ₐ[R] MvPolynomial ι T) (r : L) :
    flattenCoefficients E (C r) = flatten T ι (C (E r)) := by
  change flatten T ι (MvPolynomial.map E.toRingHom (C r)) = _
  rw [map_C]
  rfl

theorem flatten_residualRelation (E : L ≃ₐ[R] MvPolynomial ι T)
    (x g : (ι ⊕ κ) → L) (a χ : ι → Tˣ)
    (hx : ∀ i, E (x (Sum.inl i)) = X i)
    (hg : ∀ i, E (g (Sum.inl i)) = C ((a i : T) * (1 + (χ i : T)))) (i : ι) :
    flattenCoefficients E (EliminationWithResidual.residualRelation x g i) =
      RescaleExchange.rawRelation a χ i := by
  rw [EliminationWithResidual.residualRelation, map_sub, map_mul,
    flattenCoefficients_C, flattenCoefficients_X, flattenCoefficients_C, hx, hg,
    flatten_C_X, flatten_C_C]
  simp only [RescaleExchange.rawRelation, map_mul, map_add, map_one]

theorem map_residualIdeal (E : L ≃ₐ[R] MvPolynomial ι T)
    (x g : (ι ⊕ κ) → L) (a χ : ι → Tˣ)
    (hx : ∀ i, E (x (Sum.inl i)) = X i)
    (hg : ∀ i, E (g (Sum.inl i)) = C ((a i : T) * (1 + (χ i : T)))) :
    (EliminationWithResidual.residualIdeal x g).map (flattenCoefficients E).toRingHom =
      RescaleExchange.rawRelations a χ := by
  rw [EliminationWithResidual.residualIdeal, Ideal.map_span, ← Set.range_comp]
  unfold RescaleExchange.rawRelations
  apply congrArg Ideal.span
  apply congrArg Set.range
  exact funext (flatten_residualRelation E x g a χ hx hg)

def residualEquiv (E : L ≃ₐ[R] MvPolynomial ι T)
    (x g : (ι ⊕ κ) → L) (a χ : ι → Tˣ)
    (hx : ∀ i, E (x (Sum.inl i)) = X i)
    (hg : ∀ i, E (g (Sum.inl i)) = C ((a i : T) * (1 + (χ i : T)))) :
    (MvPolynomial ι L ⧸ EliminationWithResidual.residualIdeal x g) ≃ₐ[R]
      LocalExchangeSmooth.LocalAlgebra χ :=
  (Ideal.quotientEquivAlg _ _ (flattenCoefficients E) (map_residualIdeal E x g a χ hx hg).symm).trans
    ((RescaleExchange.quotientEquiv a χ).restrictScalars R)

theorem residualEquiv_original (E : L ≃ₐ[R] MvPolynomial ι T)
    (x g : (ι ⊕ κ) → L) (a χ : ι → Tˣ)
    (hx : ∀ i, E (x (Sum.inl i)) = X i)
    (hg : ∀ i, E (g (Sum.inl i)) = C ((a i : T) * (1 + (χ i : T)))) (i : ι) :
    residualEquiv E x g a χ hx hg
      (Ideal.Quotient.mk (EliminationWithResidual.residualIdeal x g) (C (x (Sum.inl i)))) =
      LocalExchangeSmooth.x χ i := by
  change RescaleExchange.quotientEquiv a χ
    (Ideal.Quotient.mk (RescaleExchange.rawRelations a χ)
      (flattenCoefficients E (C (x (Sum.inl i))))) = _
  rw [flattenCoefficients_C, hx, flatten_C_X, RescaleExchange.quotientEquiv_X_left]

def preparedOpenEquiv (E : L ≃ₐ[R] MvPolynomial ι T)
    (x g : (ι ⊕ κ) → L) (u : κ → Lˣ) (a χ : ι → Tˣ)
    (hu : ∀ k, x (Sum.inr k) = (u k : L))
    (hx : ∀ i, E (x (Sum.inl i)) = X i)
    (hg : ∀ i, E (g (Sum.inl i)) = C ((a i : T) * (1 + (χ i : T)))) :
    (MvPolynomial (ι ⊕ κ) L ⧸ StratumPresentation.exchangeIdeal x g) ≃ₐ[R]
      LocalExchangeSmooth.LocalAlgebra χ :=
  ((EliminationWithResidual.exchangeQuotientEquiv x g u hu).restrictScalars R).trans
    (residualEquiv E x g a χ hx hg)

theorem preparedOpenEquiv_original (E : L ≃ₐ[R] MvPolynomial ι T)
    (x g : (ι ⊕ κ) → L) (u : κ → Lˣ) (a χ : ι → Tˣ)
    (hu : ∀ k, x (Sum.inr k) = (u k : L))
    (hx : ∀ i, E (x (Sum.inl i)) = X i)
    (hg : ∀ i, E (g (Sum.inl i)) = C ((a i : T) * (1 + (χ i : T)))) (i : ι) :
    preparedOpenEquiv E x g u a χ hu hx hg
      (Ideal.Quotient.mk (StratumPresentation.exchangeIdeal x g) (C (x (Sum.inl i)))) =
      LocalExchangeSmooth.x χ i := by
  change residualEquiv E x g a χ hx hg
    ((EliminationWithResidual.exchangeQuotientEquiv x g u hu)
      (algebraMap L _ (x (Sum.inl i)))) = _
  rw [AlgEquiv.commutes]
  exact residualEquiv_original E x g a χ hx hg i

#print axioms flatten
#print axioms flatten_X
#print axioms flatten_C_X
#print axioms flatten_C_C
#print axioms flattenCoefficients
#print axioms flattenCoefficients_X
#print axioms flattenCoefficients_C
#print axioms flatten_residualRelation
#print axioms map_residualIdeal
#print axioms residualEquiv
#print axioms residualEquiv_original
#print axioms preparedOpenEquiv
#print axioms preparedOpenEquiv_original
end Verification.OpenChartPresentation
