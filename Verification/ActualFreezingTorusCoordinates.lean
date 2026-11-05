/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ActualFreezingCoefficient
import Verification.PrimitiveFiberCoordinates

/-!
# Actual Freezing Torus Coordinates

In the actual freezing character quotient, every torus monomial
has the expected quotient-lattice exponent and a constructed unit scalar.
This supplies the scalar coefficients of the residual frozen seed.
-/
noncomputable section
namespace Verification.ActualFreezingTorusCoordinates
open Verification.ActualFreezingCoefficient Verification.ActualFreezingConstraint
open Verification.ActualFreezingDivisor Verification.OriginalTorus
open Verification.PrimitiveCharacters
attribute [local instance] Verification.ActualFreezingConstraint.neighborFintype
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ) (v : Fin n)

def signCharacter : Multiplicative ℤ →* Rˣ :=
  basisCharacter (Basis.singleton PUnit.{1} ℤ) (fun _ => -1)

theorem torusIdeal_eq : torusIdeal R κ n B v =
    columnIdeal (columnMap κ n B v) (Basis.singleton PUnit.{1} ℤ) (signCharacter R) := by
  have hf : ∀ i : PUnit.{1}, columnMap κ n B v (Basis.singleton PUnit.{1} ℤ i) =
      ExchangeCharacters.column Finset.univ (columnEntry κ n B v) (fun a => Finsupp.single a (1 : ℤ)) := by
    intro i
    simp only [Basis.singleton_apply, columnMap, LinearMap.toSpanSingleton_apply, one_smul,
      distinguishedColumn]
  have h := ExchangeCharacters.exchange_ideal_eq_prescribed (R := R) Finset.univ
    (fun a (_ : PUnit.{1}) => columnEntry κ n B v a) (fun a => Finsupp.single a (1 : ℤ))
    (columnMap κ n B v) (Basis.singleton PUnit.{1} ℤ) hf
  change Ideal.span (Set.range (fun _ : PUnit.{1} => torusExchange R κ n B v)) = _ at h
  rw [Set.range_const] at h
  exact h.trans (prescribedIdeal_eq _ _ _)

theorem primitive_coordinates
    (hinj : Function.Injective (columnMap κ n B v))
    (hs : Verification.FreezingLattice.Saturated (LinearMap.range (columnMap κ n B v))) :
    ∃ (e : TorusFiber R κ n B v ≃ₐ[R]
        MonoidAlgebra R (Multiplicative ((OriginalTorus.Lattice (Neighbor κ n B v ⊕ κ)) ⧸
          LinearMap.range (columnMap κ n B v))))
      (d : Multiplicative (OriginalTorus.Lattice (Neighbor κ n B v ⊕ κ)) →* Rˣ),
      d (Multiplicative.ofAdd (distinguishedColumn κ n B v)) = -1 ∧
      ∀ m, e (Ideal.Quotient.mk (torusIdeal R κ n B v)
        (MonoidAlgebra.of R _ (Multiplicative.ofAdd m))) =
        algebraMap R _ (d (Multiplicative.ofAdd m) : R) *
          MonoidAlgebra.of R _ (Multiplicative.ofAdd ((LinearMap.range (columnMap κ n B v)).mkQ m)) := by
  obtain ⟨e,d,hd,he⟩ := PrimitiveFiberCoordinates.primitive_monomials (R := R)
    (columnMap κ n B v) hinj hs (Basis.singleton PUnit.{1} ℤ) (signCharacter R)
  refine ⟨(Ideal.quotientEquivAlgOfEq R (torusIdeal_eq R κ n B v)).trans e,d,?_,?_⟩
  · have h := hd 1
    have hc : signCharacter R (Multiplicative.ofAdd (1 : ℤ)) = -1 := by
      simpa only [Basis.singleton_apply] using
        (basisCharacter_apply (Basis.singleton PUnit.{1} ℤ) (fun _ => (-1 : Rˣ)) PUnit.unit)
    simpa only [columnMap, LinearMap.toSpanSingleton_apply, one_smul, hc] using h
  · intro m
    dsimp only [AlgEquiv.trans_apply]
    rw [Ideal.quotientEquivAlgOfEq_mk]
    exact he m

#print axioms signCharacter
#print axioms torusIdeal_eq
#print axioms primitive_coordinates
end Verification.ActualFreezingTorusCoordinates
