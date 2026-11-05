/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.ExchangeRing
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Exchange Open Cover

The independent-zero-set charts cover the entire prime spectrum of an
acyclic exchange presentation. This is a statement about all scheme points,
not only field-valued closed points.
-/
noncomputable section
namespace Verification.ExchangeOpenCover
open Verification.ExchangeRing Verification.ExchangeGeometry
open scoped BigOperators
variable {A : Type*} [CommRing A] {n : ℕ}

def Independent (v : Fin n → Fin n → ℕ) (I : Finset (Fin n)) : Prop :=
  ∀ i ∈ I, ∀ j ∈ I, ¬ Adjacent v i j

def chartElement (x : Fin n → A) (I : Finset (Fin n)) : A := ∏ i ∈ Iᶜ, x i

def primeZeroSet (x : Fin n → A) (p : PrimeSpectrum A) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => x i ∈ p.asIdeal)

theorem primeZeroSet_independent
    (v : Fin n → Fin n → ℕ) (x : Fin n → A)
    (hunit : ∀ i j, Adjacent v i j → Ideal.span ({x i, x j} : Set A) = ⊤)
    (p : PrimeSpectrum A) : Independent v (primeZeroSet x p) := by
  classical
  intro i hi j hj hij
  have hi' : x i ∈ p.asIdeal := by simpa only [primeZeroSet, Finset.mem_filter, Finset.mem_univ, true_and] using hi
  have hj' : x j ∈ p.asIdeal := by simpa only [primeZeroSet, Finset.mem_filter, Finset.mem_univ, true_and] using hj
  apply p.isPrime.ne_top
  apply top_unique
  rw [← hunit i j hij]
  apply Ideal.span_le.mpr
  intro a ha
  rcases ha with rfl | rfl
  · exact hi'
  · exact hj'

theorem prime_mem_own_chart (x : Fin n → A) (p : PrimeSpectrum A) :
    p ∈ PrimeSpectrum.basicOpen (chartElement x (primeZeroSet x p)) := by
  classical
  rw [PrimeSpectrum.mem_basicOpen]
  change (∏ i ∈ (primeZeroSet x p)ᶜ, x i) ∉ p.asIdeal
  rw [Ideal.IsPrime.prod_mem_iff]
  push_neg
  intro i hi
  have h := Finset.mem_compl.mp hi
  simpa only [primeZeroSet, Finset.mem_filter, Finset.mem_univ, true_and] using h

theorem independent_charts_cover
    (v : Fin n → Fin n → ℕ) (x : Fin n → A)
    (hunit : ∀ i j, Adjacent v i j → Ideal.span ({x i, x j} : Set A) = ⊤) :
    (⨆ I : {I : Finset (Fin n) // Independent v I},
      PrimeSpectrum.basicOpen (chartElement x I.1)) = ⊤ := by
  apply top_unique
  intro p _
  apply TopologicalSpace.Opens.mem_iSup.mpr
  exact ⟨⟨primeZeroSet x p, primeZeroSet_independent v x hunit p⟩, prime_mem_own_chart x p⟩

theorem chartElements_span_top
    (v : Fin n → Fin n → ℕ) (x : Fin n → A)
    (hunit : ∀ i j, Adjacent v i j → Ideal.span ({x i, x j} : Set A) = ⊤) :
    Ideal.span (Set.range (fun I : {I : Finset (Fin n) // Independent v I} => chartElement x I.1)) = ⊤ :=
  PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp (independent_charts_cover v x hunit)

theorem exchange_charts_cover
    (u v : Fin n → Fin n → ℕ) (x y c d : Fin n → A)
    (hsupport : ∀ i j, u i j = 0 ↔ v i j = 0)
    (hc : ∀ i, IsUnit (c i)) (he : ExchangeEquations u v x y c d) :
    (⨆ I : {I : Finset (Fin n) // Independent v I},
      PrimeSpectrum.basicOpen (chartElement x I.1)) = ⊤ :=
  independent_charts_cover v x (adjacent_span_eq_top u v x y c d hsupport hc he)

theorem presentation_charts_cover (R : Type*) [CommRing R]
    (u v : Fin n → Fin n → ℕ) (c d : Fin n → Rˣ)
    (hsupport : ∀ i j, u i j = 0 ↔ v i j = 0) :
    (⨆ I : {I : Finset (Fin n) // Independent v I},
      PrimeSpectrum.basicOpen (chartElement (initial R u v c d) I.1)) = ⊤ :=
  independent_charts_cover v (initial R u v c d)
    (presentation_adjacent_span_eq_top R u v c d hsupport)

#print axioms Independent
#print axioms chartElement
#print axioms primeZeroSet
#print axioms primeZeroSet_independent
#print axioms prime_mem_own_chart
#print axioms independent_charts_cover
#print axioms chartElements_span_top
#print axioms exchange_charts_cover
#print axioms presentation_charts_cover
end Verification.ExchangeOpenCover
