/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualResidualFiber
import Verification.ActualFreezingTorusCoordinates
import Verification.ActualFreezingColumnAS

/-!
# Actual Scalar Freezing

The actual freezing divisor is an affine line over a scalar exchange
presentation on the quotient frozen lattice. All scalar coefficients are
constructed from the primitive character fiber; the remaining principal
exponents are the original matrix entries.
-/
noncomputable section
namespace Verification.ActualScalarFreezing
open MvPolynomial Verification.ActualFreezingCoefficient Verification.ActualFreezingConstraint
open Verification.ActualFreezingDivisor Verification.FreezingIndex
open Verification.ActualRemainingMonomials Verification.ActualResidualFiber
open Verification.FrozenAcyclicCover
open scoped BigOperators
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Verification.ActualFreezingConstraint.neighborFintype
attribute [local instance] Verification.ActualFreezingConstraint.remainingFintype
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (v : Fin n)

abbrev FrozenLattice := (Neighbor κ n B v ⊕ κ) →₀ ℤ
abbrev QuotientLattice := FrozenLattice κ n B v ⧸ LinearMap.range (columnMap κ n B v)
abbrev Coefficients := MonoidAlgebra R (Multiplicative (QuotientLattice κ n B v))

def coefficientExponent (p : (Fin n ⊕ κ) → ℕ) : FrozenLattice κ n B v :=
  ∑ a : Neighbor κ n B v ⊕ κ,
    p (ActualDivisorPresentation.invertedOriginal κ n B v a) • Finsupp.single a (1 : ℤ)

theorem coefficientMonomial_eq (p : (Fin n ⊕ κ) → ℕ) :
    coefficientMonomial R κ n B v p = ExchangeCharacters.monomial (coefficientExponent κ n B v p) := by
  symm
  rw [coefficientExponent, ExchangeCharacters.monomial_sum]
  apply Finset.prod_congr rfl
  intro a _
  rw [ExchangeCharacters.monomial_nsmul]
  rfl

def scalarMonomial (d : Multiplicative (FrozenLattice κ n B v) →* Rˣ)
    (m : FrozenLattice κ n B v) : Coefficients R κ n B v :=
  algebraMap R _ (d (Multiplicative.ofAdd m) : R) *
    MonoidAlgebra.of R _ (Multiplicative.ofAdd ((LinearMap.range (columnMap κ n B v)).mkQ m))

def scalarExchange (d : Multiplicative (FrozenLattice κ n B v) →* Rˣ)
    (i : Remaining κ n B v) : MvPolynomial (Remaining κ n B v) (Coefficients R κ n B v) :=
  C (scalarMonomial R κ n B v d (coefficientExponent κ n B v (fun a => (B a (Sum.inl i.val)).toNat))) *
      (∏ a : Remaining κ n B v, X a ^ (B (Sum.inl a.val) (Sum.inl i.val)).toNat) +
    C (scalarMonomial R κ n B v d (coefficientExponent κ n B v (fun a => (-B a (Sum.inl i.val)).toNat))) *
      (∏ a : Remaining κ n B v, X a ^ (-B (Sum.inl a.val) (Sum.inl i.val)).toNat)

def scalarRelation (d : Multiplicative (FrozenLattice κ n B v) →* Rˣ)
    (i : Remaining κ n B v) : MvPolynomial (Remaining κ n B v)
      (MvPolynomial (Remaining κ n B v) (Coefficients R κ n B v)) :=
  C (X i) * X i - C (scalarExchange R κ n B v d i)

def scalarRelations (d : Multiplicative (FrozenLattice κ n B v) →* Rˣ) :
    Ideal (MvPolynomial (Remaining κ n B v)
      (MvPolynomial (Remaining κ n B v) (Coefficients R κ n B v))) :=
  Ideal.span (Set.range (scalarRelation R κ n B v d))

local instance scalarPolynomialCommRing : CommRing
    (MvPolynomial (Remaining κ n B v) (MvPolynomial (Remaining κ n B v) (Coefficients R κ n B v))) :=
  inferInstance

abbrev ScalarResidual (d : Multiplicative (FrozenLattice κ n B v) →* Rˣ) :=
  MvPolynomial (Remaining κ n B v) (MvPolynomial (Remaining κ n B v) (Coefficients R κ n B v)) ⧸
    scalarRelations R κ n B v d

variable (e : TorusFiber R κ n B v ≃ₐ[R] Coefficients R κ n B v)
variable (d : Multiplicative (FrozenLattice κ n B v) →* Rˣ)
variable (he : ∀ m, e (Ideal.Quotient.mk (torusIdeal R κ n B v)
    (MonoidAlgebra.of R _ (Multiplicative.ofAdd m))) = scalarMonomial R κ n B v d m)
include he

theorem coefficient_image (p : (Fin n ⊕ κ) → ℕ) :
    e (Ideal.Quotient.mk (torusIdeal R κ n B v) (coefficientMonomial R κ n B v p)) =
      scalarMonomial R κ n B v d (coefficientExponent κ n B v p) := by
  rw [coefficientMonomial_eq]
  exact he _

theorem exchange_image (i : Remaining κ n B v) :
    mapAlgEquiv (Remaining κ n B v) e (reducedExchange R κ n B v i) = scalarExchange R κ n B v d i := by
  change MvPolynomial.map e.toRingHom (MvPolynomial.map (Ideal.Quotient.mk (torusIdeal R κ n B v))
    (remainingExchange R κ n B v i)) = _
  simp only [remainingExchange, map_add, map_mul, map_C, retainedMonomial, map_prod,
    map_pow, map_X]
  change C (e (Ideal.Quotient.mk _ (coefficientMonomial R κ n B v _))) * _ +
    C (e (Ideal.Quotient.mk _ (coefficientMonomial R κ n B v _))) * _ = _
  rw [coefficient_image R κ n B v e d he, coefficient_image R κ n B v e d he]
  rfl

theorem map_relations :
    (relations R κ n B v).map
      (mapAlgEquiv (Remaining κ n B v) (mapAlgEquiv (Remaining κ n B v) e)).toRingHom =
      scalarRelations R κ n B v d := by
  rw [relations, Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  change MvPolynomial.map (mapAlgEquiv (Remaining κ n B v) e).toRingHom (relation R κ n B v i) = _
  simp only [relation, map_sub, map_mul, map_C, map_X]
  change C (mapAlgEquiv (Remaining κ n B v) e (X i)) * X i -
    C (mapAlgEquiv (Remaining κ n B v) e (reducedExchange R κ n B v i)) = _
  rw [exchange_image R κ n B v e d he]
  change C (MvPolynomial.map e.toRingHom (X i)) * X i - C (scalarExchange R κ n B v d i) = _
  rw [map_X]
  rfl

def scalarEquiv : FiberResidual R κ n B v ≃ₐ[R] ScalarResidual R κ n B v d :=
  Ideal.quotientEquivAlg _ _
    (mapAlgEquiv (Remaining κ n B v) (mapAlgEquiv (Remaining κ n B v) e))
      (map_relations R κ n B v e d he).symm

omit he e d in
theorem actual_scalar_freezing
    (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
    (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
    (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
    (hAS : AnticliqueSubcolumns.AS (fun a w => B a (Sum.inl w)) ({v} : Finset (Fin n))) :
    ∃ d : Multiplicative (FrozenLattice κ n B v) →* Rˣ,
      d (Multiplicative.ofAdd (distinguishedColumn κ n B v)) = -1 ∧
      Nonempty (Divisor R κ n B v ≃ₐ[R] Polynomial (ScalarResidual R κ n B v d)) := by
  have ha := ActualFreezingColumnAS.singleton_AS κ n B v hpos hneg hsupport hAS
  obtain ⟨e,d,hd,he⟩ := ActualFreezingTorusCoordinates.primitive_coordinates R κ n B v ha.1 ha.2
  exact ⟨d,hd,⟨(ActualResidualFiber.divisorEquiv R κ n B v hpos hneg hsupport).trans
    (Polynomial.mapAlgEquiv (scalarEquiv R κ n B v e d he))⟩⟩

#print axioms FrozenLattice
#print axioms QuotientLattice
#print axioms Coefficients
#print axioms coefficientExponent
#print axioms coefficientMonomial_eq
#print axioms scalarMonomial
#print axioms scalarExchange
#print axioms scalarRelation
#print axioms scalarRelations
#print axioms scalarPolynomialCommRing
#print axioms ScalarResidual
#print axioms coefficient_image
#print axioms exchange_image
#print axioms map_relations
#print axioms scalarEquiv
#print axioms actual_scalar_freezing
end Verification.ActualScalarFreezing
