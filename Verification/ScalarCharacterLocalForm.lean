/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ScalarExchangeCharacters

/-!
# Scalar Character Local Form

The scalar exchange equation in an independent chart has the form
x*y = u*(1+chi), with both u and chi explicitly constructed units.
-/
noncomputable section
namespace Verification.ScalarCharacterLocalForm
open Verification.ExchangeCharacters
variable {R M α : Type*} [CommRing R] [AddCommGroup M]

def coefficientUnit (s : Finset α) (B : α → ℤ) (e : α → M) (b : Rˣ) :
    (MonoidAlgebra R (Multiplicative M))ˣ :=
  Units.map (algebraMap R _).toMonoidHom b * negativeUnit s B e

def characterUnit (s : Finset α) (B : α → ℤ) (e : α → M) (a b : Rˣ) :
    (MonoidAlgebra R (Multiplicative M))ˣ :=
  Units.map (algebraMap R _).toMonoidHom (a * b⁻¹) *
    (MonoidAlgebra.of R (Multiplicative M)).toHomUnits (Multiplicative.ofAdd (column s B e))

theorem exchange_form (s : Finset α) (B : α → ℤ) (e : α → M) (a b : Rˣ) :
    ScalarExchangeCharacters.exchange s B e a b =
      (coefficientUnit s B e b : MonoidAlgebra R (Multiplicative M)) *
        (1 + (characterUnit s B e a b : MonoidAlgebra R (Multiplicative M))) := by
  change algebraMap R _ (a : R) * (∏ i ∈ s, monomial (e i) ^ (B i).toNat) +
    algebraMap R _ (b : R) * (∏ i ∈ s, monomial (e i) ^ (-B i).toNat) =
      (algebraMap R _ (b : R) * monomial (negative s B e)) *
        (1 + algebraMap R _ ((a * b⁻¹ : Rˣ) : R) * monomial (column s B e))
  rw [← positive_monomial, ← negative_monomial, positive_eq_negative_add_column, monomial_add]
  simp only [Units.val_mul,map_mul]
  have hu : algebraMap R (MonoidAlgebra R (Multiplicative M)) (b : R) *
      algebraMap R _ (b⁻¹ : Rˣ) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  linear_combination -(algebraMap R (MonoidAlgebra R (Multiplicative M)) (a : R) *
    monomial (negative s B e) * monomial (column s B e)) * hu

#print axioms coefficientUnit
#print axioms characterUnit
#print axioms exchange_form
end Verification.ScalarCharacterLocalForm
