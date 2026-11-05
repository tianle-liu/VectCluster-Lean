/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualFreezingConstraint
import Verification.PolynomialCoefficientAlgebra

/-!
# Actual Freezing Coefficient

Impose the actual equation at the removed vertex on the coefficient
base. Its quotient is a polynomial ring over the actual torus character
fiber; a primitive original column gives the split quotient-lattice torus.
-/
noncomputable section
namespace Verification.ActualFreezingCoefficient
open MvPolynomial Verification.ActualFreezingBase Verification.ActualFreezingFactor
open Verification.ActualFreezingConstraint Verification.ActualFreezingDivisor
open Verification.FreezingIndex Verification.OriginalTorus Verification.FrozenAcyclicCover
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Verification.ActualFreezingConstraint.neighborFintype
attribute [local instance] Verification.ActualFreezingConstraint.remainingFintype
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (v : Fin n)

def constraintIdeal : Ideal (Base R κ n B v) :=
  Ideal.span {exchange R κ n B v (Sum.inl (Sum.inl PUnit.unit))}

def torusIdeal : Ideal (Torus R (Neighbor κ n B v ⊕ κ)) :=
  Ideal.span {torusExchange R κ n B v}

abbrev ConstrainedBase := Base R κ n B v ⧸ constraintIdeal R κ n B v
abbrev TorusFiber := Torus R (Neighbor κ n B v ⊕ κ) ⧸ torusIdeal R κ n B v

def distinguishedColumn : OriginalTorus.Lattice (Neighbor κ n B v ⊕ κ) :=
  ExchangeCharacters.column Finset.univ (columnEntry κ n B v) (fun a => Finsupp.single a (1 : ℤ))

def columnMap : ℤ →ₗ[ℤ] OriginalTorus.Lattice (Neighbor κ n B v ⊕ κ) :=
  LinearMap.toSpanSingleton ℤ _ (distinguishedColumn κ n B v)

variable (hpos : ∀ a i : Fin n, ¬ a < i → (B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hneg : ∀ a i : Fin n, ¬ i < a → (-B (Sum.inl a) (Sum.inl i)).toNat = 0)
variable (hsupport : ∀ i j, earlierWeights κ n B i j = 0 ↔ laterWeights κ n B i j = 0)
include hpos hneg hsupport

theorem map_constraintIdeal :
    (constraintIdeal R κ n B v).map (baseEquiv R κ n B v).toRingHom =
      Verification.PolynomialQuotient.coefficientIdeal
        (α := Remaining κ n B v) (torusIdeal R κ n B v) := by
  rw [constraintIdeal, Ideal.map_span, Set.image_singleton]
  change Ideal.span {baseEquiv R κ n B v (exchange R κ n B v (Sum.inl (Sum.inl PUnit.unit)))} = _
  rw [exchange_image R κ n B v hpos hneg hsupport]
  rw [Verification.PolynomialQuotient.coefficientIdeal, torusIdeal,
    Ideal.map_span, Set.image_singleton]

def constrainedEquiv : ConstrainedBase R κ n B v ≃ₐ[R]
    MvPolynomial (Remaining κ n B v) (TorusFiber R κ n B v) :=
  (Ideal.quotientEquivAlg _ _ (baseEquiv R κ n B v)
    (map_constraintIdeal R κ n B v hpos hneg hsupport).symm).trans
      ((Verification.PolynomialCoefficientAlgebra.coefficientEquiv (torusIdeal R κ n B v)).restrictScalars R)

theorem constrainedEquiv_mk (p : Base R κ n B v) :
    constrainedEquiv R κ n B v hpos hneg hsupport
      (Ideal.Quotient.mk (constraintIdeal R κ n B v) p) =
      MvPolynomial.map (Ideal.Quotient.mk (torusIdeal R κ n B v)) (baseEquiv R κ n B v p) := rfl

omit hpos hneg hsupport in
theorem primitive_torusFiber
    (hinj : Function.Injective (columnMap κ n B v))
    (hs : Verification.FreezingLattice.Saturated (LinearMap.range (columnMap κ n B v))) :
    Nonempty (TorusFiber R κ n B v ≃ₐ[R]
      MonoidAlgebra R (Multiplicative ((OriginalTorus.Lattice (Neighbor κ n B v ⊕ κ)) ⧸
        LinearMap.range (columnMap κ n B v)))) := by
  have hf : ∀ i : PUnit.{1}, columnMap κ n B v (Basis.singleton PUnit.{1} ℤ i) =
      ExchangeCharacters.column Finset.univ (columnEntry κ n B v) (fun a => Finsupp.single a (1 : ℤ)) := by
    intro i
    simp only [Basis.singleton_apply, columnMap, LinearMap.toSpanSingleton_apply, one_smul,
      distinguishedColumn]
  have heq : (Set.range (fun _ : PUnit.{1} => torusExchange R κ n B v)) =
      {torusExchange R κ n B v} := Set.range_const
  have h := ExchangeCharacters.primitive_exchange_fiber (R := R) Finset.univ
    (fun a (_ : PUnit.{1}) => columnEntry κ n B v a) (fun a => Finsupp.single a (1 : ℤ))
    (columnMap κ n B v) (Basis.singleton PUnit.{1} ℤ) hf hinj hs
  change Nonempty ((Torus R (Neighbor κ n B v ⊕ κ) ⧸
    Ideal.span (Set.range (fun _ : PUnit.{1} => torusExchange R κ n B v))) ≃ₐ[R] _) at h
  rw [heq] at h
  exact h

theorem primitive_constrainedBase
    (hinj : Function.Injective (columnMap κ n B v))
    (hs : Verification.FreezingLattice.Saturated (LinearMap.range (columnMap κ n B v))) :
    Nonempty (ConstrainedBase R κ n B v ≃ₐ[R]
      MvPolynomial (Remaining κ n B v)
        (MonoidAlgebra R (Multiplicative ((OriginalTorus.Lattice (Neighbor κ n B v ⊕ κ)) ⧸
          LinearMap.range (columnMap κ n B v))))) := by
  obtain ⟨e⟩ := primitive_torusFiber R κ n B v hinj hs
  exact ⟨(constrainedEquiv R κ n B v hpos hneg hsupport).trans (mapAlgEquiv _ e)⟩

#print axioms constraintIdeal
#print axioms torusIdeal
#print axioms ConstrainedBase
#print axioms TorusFiber
#print axioms distinguishedColumn
#print axioms columnMap
#print axioms map_constraintIdeal
#print axioms constrainedEquiv
#print axioms constrainedEquiv_mk
#print axioms primitive_torusFiber
#print axioms primitive_constrainedBase
end Verification.ActualFreezingCoefficient
