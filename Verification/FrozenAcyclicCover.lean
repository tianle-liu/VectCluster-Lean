/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FrozenOpenChart
import Verification.ExchangeOpenCover

/-!
# Frozen Acyclic Cover

The independent-set cover for the literal all-row exchange equations.
All mutable coordinates are fixed once and for all in their acyclic order;
only the frozen coordinates are inverted in this global presentation.
-/
noncomputable section
namespace Verification.FrozenAcyclicCover
open MvPolynomial Verification.ActualStratum Verification.StratumPresentation
open Verification.ExchangeGeometry Verification.ExchangeOpenCover
open scoped BigOperators
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)

def noMutable : Empty → κ := Empty.elim
abbrev PolynomialPresentation := FrozenOpenChart.Presentation R (Fin n) κ Empty (noMutable κ) B
instance presentationCommRing : CommRing (PolynomialPresentation R κ n B) := inferInstance

def Global := FrozenOpenChart.FrozenPresentation R (Fin n) κ Empty (noMutable κ) B

instance globalCommRing : CommRing (Global R κ n B) :=
  inferInstanceAs (CommRing (FrozenOpenChart.FrozenPresentation R (Fin n) κ Empty (noMutable κ) B))

instance globalAlgebra : Algebra (PolynomialPresentation R κ n B) (Global R κ n B) :=
  inferInstanceAs (Algebra (PolynomialPresentation R κ n B)
    (FrozenOpenChart.FrozenPresentation R (Fin n) κ Empty (noMutable κ) B))

instance globalLocalization : IsLocalization
    (FrozenOpenChart.frozenMonoid R (Fin n) κ Empty (noMutable κ) B) (Global R κ n B) :=
  inferInstanceAs (IsLocalization
    (FrozenOpenChart.frozenMonoid R (Fin n) κ Empty (noMutable κ) B)
    (FrozenOpenChart.FrozenPresentation R (Fin n) κ Empty (noMutable κ) B))

def initial (v : Fin n ⊕ κ) : Global R κ n B :=
  algebraMap (PolynomialPresentation R κ n B) (Global R κ n B)
    (FrozenOpenChart.original R (Fin n) κ Empty (noMutable κ) B v)

def mutated (i : Fin n) : Global R κ n B :=
  algebraMap (PolynomialPresentation R κ n B) (Global R κ n B)
    (Ideal.Quotient.mk _ (X (Sum.inl i)))

def presentationMap : MvPolynomial (Fin n ⊕ Empty) (OriginalPolynomial R (Fin n) κ) →+* Global R κ n B :=
  (algebraMap (PolynomialPresentation R κ n B) (Global R κ n B)).comp (Ideal.Quotient.mk _)

def coefficientMap : OriginalPolynomial R (Fin n) κ →+* Global R κ n B :=
  (presentationMap R κ n B).comp C

theorem coefficientMap_X (v : Fin n ⊕ κ) : coefficientMap R κ n B (X v) = initial R κ n B v := rfl

def earlierWeights (a i : Fin n) : ℕ := (B (Sum.inl a) (Sum.inl i)).toNat
def laterWeights (i a : Fin n) : ℕ := (-B (Sum.inl a) (Sum.inl i)).toNat

def earlierCoefficient (i : Fin n) : Global R κ n B :=
  ∏ k, initial R κ n B (Sum.inr k) ^ (B (Sum.inr k) (Sum.inl i)).toNat

def laterCoefficient (i : Fin n) : Global R κ n B :=
  ∏ k, initial R κ n B (Sum.inr k) ^ (-B (Sum.inr k) (Sum.inl i)).toNat

theorem frozen_unit (k : κ) : IsUnit (initial R κ n B (Sum.inr k)) := by
  apply IsLocalization.map_units (Global R κ n B)
    (⟨FrozenOpenChart.original R (Fin n) κ Empty (noMutable κ) B (Sum.inr k), ?_⟩ :
      FrozenOpenChart.frozenMonoid R (Fin n) κ Empty (noMutable κ) B)
  apply Submonoid.subset_closure
  exact ⟨⟨k, by simp [noMutable]⟩, rfl⟩

theorem earlierCoefficient_unit (i : Fin n) : IsUnit (earlierCoefficient R κ n B i) :=
  by
    apply IsUnit.prod_iff.mpr
    intro k _
    exact (frozen_unit R κ n B k).pow _

theorem literal_equation (i : Fin n) :
    initial R κ n B (Sum.inl i) * mutated R κ n B i =
      (∏ a, initial R κ n B a ^ (B a (Sum.inl i)).toNat) +
        ∏ a, initial R κ n B a ^ (-B a (Sum.inl i)).toNat := by
  have hm : exchangeRelation (initialPolynomial R (Fin n) κ Empty (noMutable κ))
      (exchangePolynomial R (Fin n) κ Empty B) (Sum.inl i) ∈
      exchangeIdeal (initialPolynomial R (Fin n) κ Empty (noMutable κ))
        (exchangePolynomial R (Fin n) κ Empty B) := Ideal.subset_span (Set.mem_range_self _)
  have hz : presentationMap R κ n B
      (exchangeRelation (initialPolynomial R (Fin n) κ Empty (noMutable κ))
        (exchangePolynomial R (Fin n) κ Empty B) (Sum.inl i)) = 0 := by
    change algebraMap (PolynomialPresentation R κ n B) (Global R κ n B)
      (Ideal.Quotient.mk _ _) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hm, map_zero]
  apply sub_eq_zero.mp
  simp only [exchangeRelation, map_sub, map_mul] at hz
  change initial R κ n B (Sum.inl i) * mutated R κ n B i -
    coefficientMap R κ n B (exchangePolynomial R (Fin n) κ Empty B (Sum.inl i)) = 0 at hz
  simpa only [exchangePolynomial, map_add, map_prod, map_pow, coefficientMap_X] using hz

theorem ordered_equations
    (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
    (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0) :
    ExchangeEquations (earlierWeights κ n B) (laterWeights κ n B)
      (fun i => initial R κ n B (Sum.inl i)) (mutated R κ n B)
      (earlierCoefficient R κ n B) (laterCoefficient R κ n B) := by
  intro i
  rw [literal_equation, Fintype.prod_sum_type, Fintype.prod_sum_type]
  unfold earlierCoefficient laterCoefficient earlierMonomial laterMonomial
  congr 1 <;> rw [mul_comm] <;> congr 1
  · apply Finset.prod_congr rfl
    intro a _
    by_cases ha : a < i
    · simp only [ha, if_true, earlierWeights]
    · simp only [ha, if_false, hpos a i ha]
  · apply Finset.prod_congr rfl
    intro a _
    by_cases ha : i < a
    · simp only [ha, if_true, laterWeights]
    · simp only [ha, if_false, hneg a i ha]

theorem global_charts_cover
    (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
    (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
    (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0) :
    (⨆ I : {I : Finset (Fin n) // Independent (laterWeights κ n B) I},
      PrimeSpectrum.basicOpen (chartElement (fun i => initial R κ n B (Sum.inl i)) I.1)) = ⊤ :=
  exchange_charts_cover (earlierWeights κ n B) (laterWeights κ n B) _ _ _ _ hsupport
    (earlierCoefficient_unit R κ n B) (ordered_equations R κ n B hpos hneg)

#print axioms noMutable
#print axioms PolynomialPresentation
#print axioms presentationCommRing
#print axioms Global
#print axioms globalCommRing
#print axioms globalAlgebra
#print axioms globalLocalization
#print axioms initial
#print axioms mutated
#print axioms presentationMap
#print axioms coefficientMap
#print axioms coefficientMap_X
#print axioms earlierWeights
#print axioms laterWeights
#print axioms earlierCoefficient
#print axioms laterCoefficient
#print axioms frozen_unit
#print axioms earlierCoefficient_unit
#print axioms literal_equation
#print axioms ordered_equations
#print axioms global_charts_cover
end Verification.FrozenAcyclicCover
