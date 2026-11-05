/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarFreezingFactor
import Verification.ScalarExchangeCharacters
import Verification.ActualRemainingMonomials
import Verification.ActualFreezingCoefficient
import Verification.PrimitiveFiberCoordinates
import Verification.PolynomialCoefficientAlgebra

/-!
# Scalar Freezing Coefficient

Impose the actual equation at the removed vertex on the coefficient
base. Its quotient is a polynomial ring over the actual torus character
fiber; a primitive original column gives the split quotient-lattice torus.
-/
noncomputable section
namespace Verification.ScalarFreezingCoefficient
open MvPolynomial Verification.ActualFreezingBase Verification.ActualFreezingFactor
open Verification.ActualFreezingConstraint (columnEntry)
open Verification.ActualFreezingDivisor
open Verification.ActualFreezingCoefficient (columnMap distinguishedColumn)
open Verification.ScalarFreezingFactor (exchange)
open Verification.FreezingIndex Verification.OriginalTorus Verification.FrozenAcyclicCover
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Verification.ActualFreezingConstraint.neighborFintype
attribute [local instance] Verification.ActualFreezingConstraint.remainingFintype
attribute [local instance] Verification.ActualFreezingConstraint.coefficientSelfAction
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (a b : Fin n → Rˣ) (v : Fin n)

def torusExchange : Torus R (Neighbor κ n B v ⊕ κ) :=
  ScalarExchangeCharacters.exchange Finset.univ (columnEntry κ n B v)
    (fun q => Finsupp.single q 1) (a v) (b v)

def remainingExchange (i : Remaining κ n B v) :
    MvPolynomial (Remaining κ n B v) (Torus R (Neighbor κ n B v ⊕ κ)) :=
  C (algebraMap R _ (a i.val : R) * ActualRemainingMonomials.coefficientMonomial R κ n B v
      (fun q => (B q (Sum.inl i.val)).toNat)) *
    ActualRemainingMonomials.retainedMonomial R κ n B v (fun q => (B q (Sum.inl i.val)).toNat) +
  C (algebraMap R _ (b i.val : R) * ActualRemainingMonomials.coefficientMonomial R κ n B v
      (fun q => (-B q (Sum.inl i.val)).toNat)) *
    ActualRemainingMonomials.retainedMonomial R κ n B v (fun q => (-B q (Sum.inl i.val)).toNat)

omit [Fintype κ] in
theorem base_scalar (r : R) :
    baseEquiv R κ n B v (LocallyClosedPresentation.baseMap
      (ActualDivisorPresentation.coefficientZeroIdeal R κ n v)
      (ActualDivisorPresentation.invertedCoefficient R κ n B v) (C r)) = C (algebraMap R _ r) :=
  (baseEquiv R κ n B v).commutes r

def constraintIdeal : Ideal (Base R κ n B v) :=
  Ideal.span {ScalarFreezingFactor.exchange R κ n B a b v (Sum.inl (Sum.inl PUnit.unit))}

def torusIdeal : Ideal (Torus R (Neighbor κ n B v ⊕ κ)) :=
  Ideal.span {torusExchange R κ n B a b v}

abbrev ConstrainedBase := Base R κ n B v ⧸ constraintIdeal R κ n B a b v
abbrev TorusFiber := Torus R (Neighbor κ n B v ⊕ κ) ⧸ torusIdeal R κ n B a b v

variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
include hpos hneg hsupport

theorem exchange_image :
    baseEquiv R κ n B v (ScalarFreezingFactor.exchange R κ n B a b v (Sum.inl (Sum.inl PUnit.unit))) =
      C (torusExchange R κ n B a b v) := by
  have hd := FreezingSupport.diagonal κ n B hpos hneg v
  have hr := FreezingSupport.remaining_column κ n B hpos hneg hsupport v
  change baseEquiv R κ n B v (LocallyClosedPresentation.baseMap _ _
    (ScalarFrozenGlobal.scalarExchange R κ n B a b v)) = _
  simp only [ScalarFrozenGlobal.scalarExchange, map_add, map_mul]
  rw [base_scalar, base_scalar]
  rw [ActualFreezingConstraint.map_monomial R κ n B v _ (by rw [hd]; rfl) (fun i => by rw [hr i]; rfl)]
  rw [ActualFreezingConstraint.map_monomial R κ n B v _ (by rw [hd]; rfl) (fun i => by rw [hr i]; rfl)]
  simp only [torusExchange, ScalarExchangeCharacters.exchange, Finset.mem_univ,
    Finset.prod_const, Finset.card_univ, columnEntry, map_add, map_mul]
  rfl

theorem remaining_exchange_image (i : Remaining κ n B v) :
    baseEquiv R κ n B v (ScalarFreezingFactor.exchange R κ n B a b v (Sum.inl (Sum.inr i))) =
      remainingExchange R κ n B a b v i := by
  have hz := FreezingSupport.remaining_row κ n B hpos hneg hsupport v i
  change baseEquiv R κ n B v (LocallyClosedPresentation.baseMap _ _
    (ScalarFrozenGlobal.scalarExchange R κ n B a b i.val)) = _
  simp only [ScalarFrozenGlobal.scalarExchange, map_add, map_mul]
  rw [base_scalar, base_scalar]
  rw [ActualRemainingMonomials.map_monomial R κ n B v _ (by rw [hz]; rfl)]
  rw [ActualRemainingMonomials.map_monomial R κ n B v _ (by rw [hz]; rfl)]
  simp only [remainingExchange, map_mul, mul_assoc]

theorem map_constraintIdeal :
    (constraintIdeal R κ n B a b v).map (baseEquiv R κ n B v).toRingHom =
      Verification.PolynomialQuotient.coefficientIdeal
        (α := Remaining κ n B v) (torusIdeal R κ n B a b v) := by
  rw [constraintIdeal, Ideal.map_span, Set.image_singleton]
  change Ideal.span {baseEquiv R κ n B v (ScalarFreezingFactor.exchange R κ n B a b v (Sum.inl (Sum.inl PUnit.unit)))} = _
  rw [exchange_image R κ n B a b v hpos hneg hsupport]
  rw [Verification.PolynomialQuotient.coefficientIdeal, torusIdeal,
    Ideal.map_span, Set.image_singleton]

def constrainedEquiv : ConstrainedBase R κ n B a b v ≃ₐ[R]
    MvPolynomial (Remaining κ n B v) (TorusFiber R κ n B a b v) :=
  (Ideal.quotientEquivAlg _ _ (baseEquiv R κ n B v)
    (map_constraintIdeal R κ n B a b v hpos hneg hsupport).symm).trans
      ((Verification.PolynomialCoefficientAlgebra.coefficientEquiv (torusIdeal R κ n B a b v)).restrictScalars R)

theorem constrainedEquiv_mk (p : Base R κ n B v) :
    constrainedEquiv R κ n B a b v hpos hneg hsupport
      (Ideal.Quotient.mk (constraintIdeal R κ n B a b v) p) =
      MvPolynomial.map (Ideal.Quotient.mk (torusIdeal R κ n B a b v)) (baseEquiv R κ n B v p) := rfl

omit hpos hneg hsupport in
def scalarCharacter : Multiplicative ℤ →* Rˣ :=
  PrimitiveCharacters.basisCharacter (Basis.singleton PUnit.{1} ℤ)
    (fun _ => ScalarExchangeCharacters.prescribed (a v) (b v))

omit hpos hneg hsupport in
theorem torusIdeal_eq : torusIdeal R κ n B a b v =
    PrimitiveCharacters.columnIdeal (columnMap κ n B v) (Basis.singleton PUnit.{1} ℤ)
      (scalarCharacter R n a b v) := by
  have hf : ∀ i : PUnit.{1}, columnMap κ n B v (Basis.singleton PUnit.{1} ℤ i) =
      ExchangeCharacters.column Finset.univ (columnEntry κ n B v) (fun q => Finsupp.single q (1 : ℤ)) := by
    intro i
    simp only [Basis.singleton_apply, columnMap, LinearMap.toSpanSingleton_apply, one_smul, distinguishedColumn]
  have h := ScalarExchangeCharacters.exchange_ideal_eq_prescribed (R := R) Finset.univ
    (fun q (_ : PUnit.{1}) => columnEntry κ n B v q) (fun q => Finsupp.single q (1 : ℤ))
    (fun _ => a v) (fun _ => b v) (columnMap κ n B v) (Basis.singleton PUnit.{1} ℤ) hf
  change Ideal.span (Set.range (fun _ : PUnit.{1} => torusExchange R κ n B a b v)) = _ at h
  rw [Set.range_const] at h
  exact h.trans (PrimitiveCharacters.prescribedIdeal_eq _ _ _)

omit hpos hneg hsupport in
theorem primitive_coordinates
    (hinj : Function.Injective (columnMap κ n B v))
    (hs : Verification.FreezingLattice.Saturated (LinearMap.range (columnMap κ n B v))) :
    ∃ (e : TorusFiber R κ n B a b v ≃ₐ[R]
        MonoidAlgebra R (Multiplicative ((OriginalTorus.Lattice (Neighbor κ n B v ⊕ κ)) ⧸
          LinearMap.range (columnMap κ n B v))))
      (d : Multiplicative (OriginalTorus.Lattice (Neighbor κ n B v ⊕ κ)) →* Rˣ),
      d (Multiplicative.ofAdd (distinguishedColumn κ n B v)) = ScalarExchangeCharacters.prescribed (a v) (b v) ∧
      ∀ m, e (Ideal.Quotient.mk (torusIdeal R κ n B a b v)
        (MonoidAlgebra.of R _ (Multiplicative.ofAdd m))) =
        algebraMap R _ (d (Multiplicative.ofAdd m) : R) *
          MonoidAlgebra.of R _ (Multiplicative.ofAdd ((LinearMap.range (columnMap κ n B v)).mkQ m)) := by
  obtain ⟨e,d,hd,he⟩ := PrimitiveFiberCoordinates.primitive_monomials (R := R)
    (columnMap κ n B v) hinj hs (Basis.singleton PUnit.{1} ℤ) (scalarCharacter R n a b v)
  refine ⟨(Ideal.quotientEquivAlgOfEq R (torusIdeal_eq R κ n B a b v)).trans e,d,?_,?_⟩
  · have h := hd 1
    have hc : scalarCharacter R n a b v (Multiplicative.ofAdd (1 : ℤ)) =
        ScalarExchangeCharacters.prescribed (a v) (b v) := by
      simpa only [Basis.singleton_apply] using
        (PrimitiveCharacters.basisCharacter_apply (Basis.singleton PUnit.{1} ℤ)
          (fun _ => ScalarExchangeCharacters.prescribed (a v) (b v)) PUnit.unit)
    simpa only [columnMap, LinearMap.toSpanSingleton_apply, one_smul, hc] using h
  · intro m
    dsimp only [AlgEquiv.trans_apply]
    rw [Ideal.quotientEquivAlgOfEq_mk]
    exact he m

#print axioms torusExchange
#print axioms remainingExchange
#print axioms base_scalar
#print axioms constraintIdeal
#print axioms torusIdeal
#print axioms ConstrainedBase
#print axioms TorusFiber
#print axioms exchange_image
#print axioms remaining_exchange_image
#print axioms map_constraintIdeal
#print axioms constrainedEquiv
#print axioms constrainedEquiv_mk
#print axioms scalarCharacter
#print axioms torusIdeal_eq
#print axioms primitive_coordinates
end Verification.ScalarFreezingCoefficient
