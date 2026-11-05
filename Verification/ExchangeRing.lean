/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ExchangeGeometry
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Exchange Ring

The acyclic zero-set argument upgraded to arbitrary commutative rings.
Adjacent initial coordinates generate the unit ideal, so on the actual
quotient x_i=0 every neighbor becomes a unit. The last section applies this
to a universal polynomial presentation by the exchange equations.
No identification with a cluster upper algebra or BFZ theorem is assumed.
-/

noncomputable section

namespace Verification.ExchangeRing

open Verification.ExchangeGeometry

variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}

theorem map_earlierMonomial (f : R →+* S) (u : Fin n → Fin n → ℕ)
    (x : Fin n → R) (i : Fin n) :
    f (earlierMonomial u x i) = earlierMonomial u (fun j => f (x j)) i := by
  simp only [earlierMonomial, map_prod, map_pow]

theorem map_laterMonomial (f : R →+* S) (v : Fin n → Fin n → ℕ)
    (x : Fin n → R) (i : Fin n) :
    f (laterMonomial v x i) = laterMonomial v (fun j => f (x j)) i := by
  simp only [laterMonomial, map_prod, map_pow]

theorem map_exchange_equations (f : R →+* S)
    (u v : Fin n → Fin n → ℕ) (x y c d : Fin n → R)
    (he : ExchangeEquations u v x y c d) :
    ExchangeEquations u v (fun i => f (x i)) (fun i => f (y i))
      (fun i => f (c i)) (fun i => f (d i)) := by
  intro i
  have h := congrArg f (he i)
  simpa only [map_mul, map_add, map_earlierMonomial, map_laterMonomial] using h

def Adjacent (v : Fin n → Fin n → ℕ) (i j : Fin n) : Prop :=
  (i < j ∧ v i j ≠ 0) ∨ (j < i ∧ v j i ≠ 0)

/-- The residue-field argument gives a unit ideal over every commutative ring. -/
theorem adjacent_span_eq_top
    (u v : Fin n → Fin n → ℕ) (x y c d : Fin n → R)
    (hsupport : ∀ i j, u i j = 0 ↔ v i j = 0)
    (hc : ∀ i, IsUnit (c i)) (he : ExchangeEquations u v x y c d)
    (i j : Fin n) (hij : Adjacent v i j) :
    Ideal.span ({x i, x j} : Set R) = ⊤ := by
  by_contra htop
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span ({x i, x j} : Set R)) htop
  letI : M.IsMaximal := hM
  letI : Field (R ⧸ M) := Ideal.Quotient.field M
  have hi : Ideal.Quotient.mk M (x i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span (by simp)))
  have hj : Ideal.Quotient.mk M (x j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span (by simp)))
  have hcn : ∀ a, Ideal.Quotient.mk M (c a) ≠ 0 :=
    fun a => ((hc a).map (Ideal.Quotient.mk M)).ne_zero
  have hz := zero_set_independent u v
    (fun a => Ideal.Quotient.mk M (x a)) (fun a => Ideal.Quotient.mk M (y a))
    (fun a => Ideal.Quotient.mk M (c a)) (fun a => Ideal.Quotient.mk M (d a))
    hsupport hcn (map_exchange_equations (Ideal.Quotient.mk M) u v x y c d he) i j hi hj
  rcases hij with ⟨hij, hv⟩ | ⟨hji, hv⟩
  · exact hv (hz.1 hij)
  · exact hv (hz.2 hji)

theorem neighbor_unit_of_zero
    (u v : Fin n → Fin n → ℕ) (x y c d : Fin n → R)
    (hsupport : ∀ i j, u i j = 0 ↔ v i j = 0)
    (hc : ∀ i, IsUnit (c i)) (he : ExchangeEquations u v x y c d)
    (i j : Fin n) (hij : Adjacent v i j) (hi : x i = 0) : IsUnit (x j) := by
  have ht := adjacent_span_eq_top u v x y c d hsupport hc he i j hij
  have h1 : (1 : R) ∈ Ideal.span ({x i, x j} : Set R) := by rw [ht]; trivial
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp h1
  rw [hi, mul_zero, zero_add] at hab
  exact isUnit_of_mul_eq_one_right b (x j) hab

/-- This is the freezing-divisor conclusion in the actual quotient ring. -/
theorem neighbor_unit_on_divisor
    (u v : Fin n → Fin n → ℕ) (x y c d : Fin n → R)
    (hsupport : ∀ i j, u i j = 0 ↔ v i j = 0)
    (hc : ∀ i, IsUnit (c i)) (he : ExchangeEquations u v x y c d)
    (i j : Fin n) (hij : Adjacent v i j) :
    IsUnit (Ideal.Quotient.mk (Ideal.span ({x i} : Set R)) (x j)) := by
  let f := Ideal.Quotient.mk (Ideal.span ({x i} : Set R))
  apply neighbor_unit_of_zero u v
    (fun a => f (x a)) (fun a => f (y a))
    (fun a => f (c a)) (fun a => f (d a)) hsupport
    (fun a => (hc a).map f) (map_exchange_equations f u v x y c d he) i j hij
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

section UniversalPresentation

variable (R) (n : ℕ)

abbrev PolynomialRing := MvPolynomial (Fin n ⊕ Fin n) R

def initialPolynomial (i : Fin n) : PolynomialRing R n := MvPolynomial.X (Sum.inl i)
def mutatedPolynomial (i : Fin n) : PolynomialRing R n := MvPolynomial.X (Sum.inr i)

variable {n}
variable (u v : Fin n → Fin n → ℕ) (c d : Fin n → Rˣ)

def relation (i : Fin n) : PolynomialRing R n :=
  initialPolynomial R n i * mutatedPolynomial R n i -
    (MvPolynomial.C (c i : R) * earlierMonomial u (initialPolynomial R n) i +
      MvPolynomial.C (d i : R) * laterMonomial v (initialPolynomial R n) i)

def definingIdeal : Ideal (PolynomialRing R n) := Ideal.span (Set.range (relation R u v c d))

abbrev Presentation := PolynomialRing R n ⧸ definingIdeal R u v c d

def initial (i : Fin n) : Presentation R u v c d :=
  Ideal.Quotient.mk (definingIdeal R u v c d) (initialPolynomial R n i)

def mutated (i : Fin n) : Presentation R u v c d :=
  Ideal.Quotient.mk (definingIdeal R u v c d) (mutatedPolynomial R n i)

def coefficientMap : R →+* Presentation R u v c d :=
  (Ideal.Quotient.mk (definingIdeal R u v c d)).comp MvPolynomial.C

theorem presentation_equations :
    ExchangeEquations u v (initial R u v c d) (mutated R u v c d)
      (fun i => coefficientMap R u v c d (c i : R))
      (fun i => coefficientMap R u v c d (d i : R)) := by
  intro i
  have hm : relation R u v c d i ∈ definingIdeal R u v c d :=
    Ideal.subset_span (Set.mem_range_self i)
  have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hm
  apply sub_eq_zero.mp
  simpa only [relation, map_sub, map_mul, map_add, map_earlierMonomial,
    map_laterMonomial, initial, mutated, coefficientMap, RingHom.comp_apply] using hz

theorem presentation_coefficients_units :
    ∀ i, IsUnit (coefficientMap R u v c d (c i : R)) :=
  fun i => (c i).isUnit.map (coefficientMap R u v c d)

theorem presentation_adjacent_span_eq_top
    (hsupport : ∀ i j, u i j = 0 ↔ v i j = 0)
    (i j : Fin n) (hij : Adjacent v i j) :
    Ideal.span ({initial R u v c d i, initial R u v c d j} :
      Set (Presentation R u v c d)) = ⊤ :=
  adjacent_span_eq_top u v _ _ _ _ hsupport (presentation_coefficients_units R u v c d)
    (presentation_equations R u v c d) i j hij

theorem presentation_neighbor_unit_on_divisor
    (hsupport : ∀ i j, u i j = 0 ↔ v i j = 0)
    (i j : Fin n) (hij : Adjacent v i j) :
    IsUnit (Ideal.Quotient.mk
      (Ideal.span ({initial R u v c d i} : Set (Presentation R u v c d)))
      (initial R u v c d j)) :=
  neighbor_unit_on_divisor u v _ _ _ _ hsupport (presentation_coefficients_units R u v c d)
    (presentation_equations R u v c d) i j hij

end UniversalPresentation

end Verification.ExchangeRing

-- Audit every theorem and all universal-presentation definitions.
#print axioms Verification.ExchangeRing.map_earlierMonomial
#print axioms Verification.ExchangeRing.map_laterMonomial
#print axioms Verification.ExchangeRing.map_exchange_equations
#print axioms Verification.ExchangeRing.Adjacent
#print axioms Verification.ExchangeRing.adjacent_span_eq_top
#print axioms Verification.ExchangeRing.neighbor_unit_of_zero
#print axioms Verification.ExchangeRing.neighbor_unit_on_divisor
#print axioms Verification.ExchangeRing.PolynomialRing
#print axioms Verification.ExchangeRing.initialPolynomial
#print axioms Verification.ExchangeRing.mutatedPolynomial
#print axioms Verification.ExchangeRing.relation
#print axioms Verification.ExchangeRing.definingIdeal
#print axioms Verification.ExchangeRing.Presentation
#print axioms Verification.ExchangeRing.initial
#print axioms Verification.ExchangeRing.mutated
#print axioms Verification.ExchangeRing.coefficientMap
#print axioms Verification.ExchangeRing.presentation_equations
#print axioms Verification.ExchangeRing.presentation_coefficients_units
#print axioms Verification.ExchangeRing.presentation_adjacent_span_eq_top
#print axioms Verification.ExchangeRing.presentation_neighbor_unit_on_divisor
