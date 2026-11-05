/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FrozenAcyclicCover

/-!
# Scalar Frozen Global

The literal acyclic exchange presentation with arbitrary unit scalar
coefficients in both terms, with all frozen originals inverted. This is
the input generality required for successive freezing in the manuscript.
-/
noncomputable section
namespace Verification.ScalarFrozenGlobal
open MvPolynomial Verification.ActualStratum Verification.StratumPresentation
open Verification.FrozenAcyclicCover Verification.ExchangeGeometry
open scoped BigOperators
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (a b : Fin n → Rˣ)

def scalarExchange (i : Fin n) : OriginalPolynomial R (Fin n) κ :=
  C (a i : R) * (∏ w, X w ^ (B w (Sum.inl i)).toNat) +
    C (b i : R) * (∏ w, X w ^ (-B w (Sum.inl i)).toNat)

def exchangeFamily : (Fin n ⊕ Empty) → OriginalPolynomial R (Fin n) κ :=
  Sum.elim (scalarExchange R κ n B a b) Empty.elim

abbrev Presentation := MvPolynomial (Fin n ⊕ Empty) (OriginalPolynomial R (Fin n) κ) ⧸
  exchangeIdeal (initialPolynomial R (Fin n) κ Empty (noMutable κ)) (exchangeFamily R κ n B a b)

instance presentationCommRing : CommRing (Presentation R κ n B a b) := inferInstance

def original (w : Fin n ⊕ κ) : Presentation R κ n B a b := Ideal.Quotient.mk _ (C (X w))

def frozenMonoid : Submonoid (Presentation R κ n B a b) :=
  Submonoid.closure (Set.range (fun k : κ => original R κ n B a b (Sum.inr k)))

local instance presentationSelfAction : DistribMulAction (Presentation R κ n B a b)
    (Presentation R κ n B a b) :=
  (Semiring.toModule : Module (Presentation R κ n B a b) (Presentation R κ n B a b)).toDistribMulAction

def Global := Localization (frozenMonoid R κ n B a b)

instance globalCommRing : CommRing (Global R κ n B a b) :=
  inferInstanceAs (CommRing (Localization (frozenMonoid R κ n B a b)))

instance globalAlgebra : Algebra (Presentation R κ n B a b) (Global R κ n B a b) :=
  inferInstanceAs (Algebra (Presentation R κ n B a b) (Localization (frozenMonoid R κ n B a b)))

instance globalLocalization : IsLocalization (frozenMonoid R κ n B a b) (Global R κ n B a b) :=
  inferInstanceAs (IsLocalization (frozenMonoid R κ n B a b) (Localization (frozenMonoid R κ n B a b)))

instance groundAlgebra : Algebra R (Global R κ n B a b) :=
  inferInstanceAs (Algebra R (Localization (frozenMonoid R κ n B a b)))

instance groundTower : IsScalarTower R (Presentation R κ n B a b) (Global R κ n B a b) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

def initial (w : Fin n ⊕ κ) : Global R κ n B a b :=
  algebraMap (Presentation R κ n B a b) _ (original R κ n B a b w)

def mutated (i : Fin n) : Global R κ n B a b :=
  algebraMap (Presentation R κ n B a b) _ (Ideal.Quotient.mk _ (X (Sum.inl i)))

def presentationMap : MvPolynomial (Fin n ⊕ Empty) (OriginalPolynomial R (Fin n) κ) →+* Global R κ n B a b :=
  (algebraMap (Presentation R κ n B a b) _).comp (Ideal.Quotient.mk _)

def coefficientMap : OriginalPolynomial R (Fin n) κ →+* Global R κ n B a b :=
  (presentationMap R κ n B a b).comp C

theorem coefficientMap_X (w : Fin n ⊕ κ) :
    coefficientMap R κ n B a b (X w) = initial R κ n B a b w := rfl

theorem coefficientMap_C (r : R) :
    coefficientMap R κ n B a b (C r) = algebraMap R (Global R κ n B a b) r := rfl

theorem frozen_unit (k : κ) : IsUnit (initial R κ n B a b (Sum.inr k)) := by
  apply IsLocalization.map_units (Global R κ n B a b)
    (⟨original R κ n B a b (Sum.inr k),?_⟩ : frozenMonoid R κ n B a b)
  exact Submonoid.subset_closure (Set.mem_range_self k)

def earlierCoefficient (i : Fin n) : Global R κ n B a b :=
  algebraMap R _ (a i : R) *
    ∏ k, initial R κ n B a b (Sum.inr k) ^ (B (Sum.inr k) (Sum.inl i)).toNat

def laterCoefficient (i : Fin n) : Global R κ n B a b :=
  algebraMap R _ (b i : R) *
    ∏ k, initial R κ n B a b (Sum.inr k) ^ (-B (Sum.inr k) (Sum.inl i)).toNat

theorem earlierCoefficient_unit (i : Fin n) : IsUnit (earlierCoefficient R κ n B a b i) := by
  apply ((a i).isUnit.map (algebraMap R _)).mul
  apply IsUnit.prod_iff.mpr
  intro k _
  exact (frozen_unit R κ n B a b k).pow _

theorem literal_equation (i : Fin n) :
    initial R κ n B a b (Sum.inl i) * mutated R κ n B a b i =
      algebraMap R (Global R κ n B a b) (a i : R) * (∏ w, initial R κ n B a b w ^ (B w (Sum.inl i)).toNat) +
        algebraMap R (Global R κ n B a b) (b i : R) * (∏ w, initial R κ n B a b w ^ (-B w (Sum.inl i)).toNat) := by
  have hm : exchangeRelation (initialPolynomial R (Fin n) κ Empty (noMutable κ))
      (exchangeFamily R κ n B a b) (Sum.inl i) ∈
      exchangeIdeal (initialPolynomial R (Fin n) κ Empty (noMutable κ))
        (exchangeFamily R κ n B a b) := Ideal.subset_span (Set.mem_range_self _)
  have hz : presentationMap R κ n B a b
      (exchangeRelation (initialPolynomial R (Fin n) κ Empty (noMutable κ))
        (exchangeFamily R κ n B a b) (Sum.inl i)) = 0 := by
    change algebraMap (Presentation R κ n B a b) (Global R κ n B a b) (Ideal.Quotient.mk _ _) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hm, map_zero]
  apply sub_eq_zero.mp
  simp only [exchangeRelation, map_sub, map_mul] at hz
  change initial R κ n B a b (Sum.inl i) * mutated R κ n B a b i -
    coefficientMap R κ n B a b (scalarExchange R κ n B a b i) = 0 at hz
  simpa only [scalarExchange, map_add, map_mul, map_prod, map_pow, coefficientMap_C, coefficientMap_X] using hz

theorem ordered_equations
    (hpos : ∀ r i : Fin n, ¬ r < i → (B (Sum.inl r) (Sum.inl i)).toNat = 0)
    (hneg : ∀ r i : Fin n, ¬ i < r → (-B (Sum.inl r) (Sum.inl i)).toNat = 0) :
    ExchangeEquations (earlierWeights κ n B) (laterWeights κ n B)
      (fun i => initial R κ n B a b (Sum.inl i)) (mutated R κ n B a b)
      (earlierCoefficient R κ n B a b) (laterCoefficient R κ n B a b) := by
  intro i
  have hp : (∏ r : Fin n, initial R κ n B a b (Sum.inl r) ^
      (B (Sum.inl r) (Sum.inl i)).toNat) =
      earlierMonomial (earlierWeights κ n B) (fun r => initial R κ n B a b (Sum.inl r)) i := by
    apply Finset.prod_congr rfl
    intro r _
    by_cases hr : r < i
    · simp only [earlierMonomial, earlierWeights, hr, if_true]
    · simp only [earlierMonomial, earlierWeights, hr, if_false, hpos r i hr, pow_zero]
  have hn : (∏ r : Fin n, initial R κ n B a b (Sum.inl r) ^
      (-B (Sum.inl r) (Sum.inl i)).toNat) =
      laterMonomial (laterWeights κ n B) (fun r => initial R κ n B a b (Sum.inl r)) i := by
    apply Finset.prod_congr rfl
    intro r _
    by_cases hr : i < r
    · simp only [laterMonomial, laterWeights, hr, if_true]
    · simp only [laterMonomial, laterWeights, hr, if_false, hneg r i hr, pow_zero]
  rw [literal_equation, Fintype.prod_sum_type, Fintype.prod_sum_type, hp, hn]
  unfold earlierCoefficient laterCoefficient
  ring

#print axioms scalarExchange
#print axioms exchangeFamily
#print axioms Presentation
#print axioms presentationCommRing
#print axioms original
#print axioms frozenMonoid
#print axioms presentationSelfAction
#print axioms Global
#print axioms globalCommRing
#print axioms globalAlgebra
#print axioms globalLocalization
#print axioms groundAlgebra
#print axioms groundTower
#print axioms initial
#print axioms mutated
#print axioms presentationMap
#print axioms coefficientMap
#print axioms coefficientMap_X
#print axioms coefficientMap_C
#print axioms frozen_unit
#print axioms earlierCoefficient
#print axioms laterCoefficient
#print axioms earlierCoefficient_unit
#print axioms literal_equation
#print axioms ordered_equations
end Verification.ScalarFrozenGlobal
