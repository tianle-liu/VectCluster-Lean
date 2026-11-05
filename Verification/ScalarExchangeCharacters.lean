/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ExchangeCharacters

/-!
# Scalar Exchange Characters

Unit coefficients in both exchange terms prescribe the character
value -b/a. The coefficient and negative monomial are actual units.
-/
noncomputable section
namespace Verification.ScalarExchangeCharacters
open Verification.ExchangeCharacters
open scoped BigOperators
variable {R M α P ι : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup P]

def prescribed (a b : Rˣ) : Rˣ := -(a⁻¹ * b)

def factorUnit (s : Finset α) (B : α → ℤ) (e : α → M) (a : Rˣ) :
    (MonoidAlgebra R (Multiplicative M))ˣ :=
  Units.map (algebraMap R _).toMonoidHom a * negativeUnit s B e

def exchange (s : Finset α) (B : α → ℤ) (e : α → M) (a b : Rˣ) :
    MonoidAlgebra R (Multiplicative M) :=
  algebraMap R _ (a : R) * (∏ i ∈ s, monomial (e i) ^ (B i).toNat) +
    algebraMap R _ (b : R) * (∏ i ∈ s, monomial (e i) ^ (-B i).toNat)

theorem exchange_factor (s : Finset α) (B : α → ℤ) (e : α → M) (a b : Rˣ) :
    exchange s B e a b = (factorUnit s B e a : MonoidAlgebra R (Multiplicative M)) *
      (monomial (column s B e) - algebraMap R _ (prescribed a b : R)) := by
  change algebraMap R _ (a : R) * (∏ i ∈ s, monomial (e i) ^ (B i).toNat) +
    algebraMap R _ (b : R) * (∏ i ∈ s, monomial (e i) ^ (-B i).toNat) =
      (algebraMap R _ (a : R) * monomial (negative s B e)) *
        (monomial (column s B e) - algebraMap R _ (prescribed a b : R))
  rw [← positive_monomial, ← negative_monomial, positive_eq_negative_add_column, monomial_add]
  simp only [prescribed, Units.val_neg, Units.val_mul, map_neg, map_mul, sub_neg_eq_add]
  have hu : algebraMap R (MonoidAlgebra R (Multiplicative M)) (a : R) *
      algebraMap R _ (a⁻¹ : Rˣ) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  calc
    _ = algebraMap R _ (a : R) * (monomial (negative s B e) * monomial (column s B e)) +
        (algebraMap R _ (a : R) * algebraMap R _ (a⁻¹ : Rˣ)) *
          algebraMap R _ (b : R) * monomial (negative s B e) := by rw [hu, one_mul]
    _ = _ := by ring

theorem exchange_ideal_eq_prescribed (s : Finset α) (B : α → ι → ℤ) (e : α → M)
    (a b : ι → Rˣ) (f : P →ₗ[ℤ] M) (basis : Basis ι ℤ P)
    (hf : ∀ i, f (basis i) = column s (fun r => B r i) e) :
    Ideal.span (Set.range (fun i => exchange s (fun r => B r i) e (a i) (b i))) =
      Verification.PrimitiveCharacters.prescribedIdeal f basis (fun i => prescribed (a i) (b i)) := by
  unfold Verification.PrimitiveCharacters.prescribedIdeal
  have he : (fun i => exchange s (fun r => B r i) e (a i) (b i)) =
      fun i => (factorUnit s (fun r => B r i) e (a i) : MonoidAlgebra R (Multiplicative M)) *
        (monomial (f (basis i)) - algebraMap R _ (prescribed (a i) (b i) : R)) := by
    funext i
    rw [hf, exchange_factor]
  rw [he, Verification.TranslatedStratum.unit_scaled_span]
  rfl

#print axioms prescribed
#print axioms factorUnit
#print axioms exchange
#print axioms exchange_factor
#print axioms exchange_ideal_eq_prescribed
end Verification.ScalarExchangeCharacters
