/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualScalarFreezing
import Verification.ActualResidualColumns

/-!
# Freezing Exponent Columns

The quotient exponents in the actual scalar freezing presentation
are exactly the original frozen columns reduced modulo the removed
column. This links the ring presentation to the proved residual AS map.
-/
noncomputable section
namespace Verification.FreezingExponentColumns
open Verification.ActualScalarFreezing Verification.ActualResidualColumns
open Verification.ActualFreezingDivisor Verification.ActualFreezingCoefficient
open scoped BigOperators
attribute [local instance] Verification.ActualFreezingConstraint.neighborFintype
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (v : Fin n)

theorem column_sum (w : Fin n) : ExchangeCharacters.column Finset.univ
    (fun a : Neighbor κ n B v ⊕ κ => B (ActualDivisorPresentation.invertedOriginal κ n B v a) (Sum.inl w))
    (fun a => Finsupp.single a (1 : ℤ)) = neighborColumn κ n B v w := by
  classical
  ext a
  cases a <;> simp [ExchangeCharacters.column, Finsupp.sum_apply, Finsupp.single_apply,
    Finsupp.smul_apply, neighborColumn]

theorem exponent_difference (w : Fin n) :
    coefficientExponent κ n B v (fun a => (B a (Sum.inl w)).toNat) =
      coefficientExponent κ n B v (fun a => (-B a (Sum.inl w)).toNat) + neighborColumn κ n B v w := by
  have h := ExchangeCharacters.positive_eq_negative_add_column Finset.univ
    (fun a : Neighbor κ n B v ⊕ κ => B (ActualDivisorPresentation.invertedOriginal κ n B v a) (Sum.inl w))
    (fun a => Finsupp.single a (1 : ℤ))
  rw [column_sum] at h
  simpa only [ExchangeCharacters.positive, ExchangeCharacters.negative,
    coefficientExponent, natCast_zsmul] using h

theorem quotient_exponent_difference (w : Fin n) :
    (LinearMap.range (columnMap κ n B v)).mkQ
        (coefficientExponent κ n B v (fun a => (B a (Sum.inl w)).toNat)) -
      (LinearMap.range (columnMap κ n B v)).mkQ
        (coefficientExponent κ n B v (fun a => (-B a (Sum.inl w)).toNat)) =
      (LinearMap.range (columnMap κ n B v)).mkQ (neighborColumn κ n B v w) := by
  rw [exponent_difference, map_add, add_sub_cancel_left]

def scalarUnit (d : Multiplicative (FrozenLattice κ n B v) →* Rˣ)
    (m : FrozenLattice κ n B v) : (Coefficients R κ n B v)ˣ :=
  Units.map (algebraMap R (Coefficients R κ n B v)).toMonoidHom (d (Multiplicative.ofAdd m)) *
    (MonoidAlgebra.of R (Multiplicative (QuotientLattice κ n B v))).toHomUnits
      (Multiplicative.ofAdd ((LinearMap.range (columnMap κ n B v)).mkQ m))

theorem scalarUnit_val (d : Multiplicative (FrozenLattice κ n B v) →* Rˣ)
    (m : FrozenLattice κ n B v) :
    (scalarUnit R κ n B v d m : Coefficients R κ n B v) = scalarMonomial R κ n B v d m := rfl

theorem scalarMonomial_add (d : Multiplicative (FrozenLattice κ n B v) →* Rˣ)
    (p q : FrozenLattice κ n B v) :
    scalarMonomial R κ n B v d (p+q) =
      scalarMonomial R κ n B v d p * scalarMonomial R κ n B v d q := by
  simp [scalarMonomial, mul_mul_mul_comm]

#print axioms column_sum
#print axioms exponent_difference
#print axioms quotient_exponent_difference
#print axioms scalarUnit
#print axioms scalarUnit_val
#print axioms scalarMonomial_add
end Verification.FreezingExponentColumns
