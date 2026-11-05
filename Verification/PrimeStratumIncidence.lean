/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FrozenAcyclicCover
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Data.Finset.Card

/-!
# Prime Stratum Incidence

Closure incidence for the actual coordinate-zero strata in prime spectra.
Applied to the literal global exchange ring, consecutive strata can meet
along a closure only by adding one original zero coordinate.
-/
namespace Verification.PrimeStratumIncidence
variable {A V : Type*} [CommRing A]
variable (x : V → A) (I J : Finset V)

def stratum : Set (PrimeSpectrum A) := {p | ∀ i, x i ∈ p.asIdeal ↔ i ∈ I}

theorem closure_zero {p : PrimeSpectrum A} (hp : p ∈ closure (stratum x I))
    {i : V} (hi : i ∈ I) : x i ∈ p.asIdeal := by
  have hsub : stratum x I ⊆ PrimeSpectrum.zeroLocus {x i} := by
    intro q hq
    exact (PrimeSpectrum.mem_zeroLocus q _).mpr
      (Set.singleton_subset_iff.mpr ((hq i).mpr hi))
  have hz := (closure_minimal hsub (PrimeSpectrum.isClosed_zeroLocus {x i})) hp
  exact (PrimeSpectrum.mem_zeroLocus p _).mp hz (Set.mem_singleton (x i))

theorem closure_subset_indices {p : PrimeSpectrum A}
    (hp : p ∈ closure (stratum x I)) (hq : p ∈ stratum x J) : I ⊆ J := by
  intro i hi
  exact (hq i).mp (closure_zero x I hp hi)

theorem disjoint_of_not_subset (h : ¬ I ⊆ J) :
    closure (stratum x I) ∩ stratum x J = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro p hp
  exact h (closure_subset_indices x I J hp.1 hp.2)

variable [DecidableEq V]

theorem adjacent_indices {p : PrimeSpectrum A}
    (hp : p ∈ closure (stratum x I)) (hq : p ∈ stratum x J)
    (hcard : J.card = I.card + 1) : ∃ i ∉ I, insert i I = J :=
  Finset.exists_eq_insert_iff.mpr ⟨closure_subset_indices x I J hp hq, hcard.symm⟩

theorem nonadjacent_disjoint (hcard : J.card = I.card + 1)
    (h : ∀ i ∉ I, insert i I ≠ J) : closure (stratum x I) ∩ stratum x J = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro p hp
  obtain ⟨i,hi,he⟩ := adjacent_indices x I J hp.1 hp.2 hcard
  exact h i hi he

section Actual
variable (R κ : Type) [CommRing R] [Fintype κ] (n : ℕ)
variable (B : (Fin n ⊕ κ) → (Fin n ⊕ Empty) → ℤ)

def actualStratum (I : Finset (Fin n)) : Set (PrimeSpectrum (FrozenAcyclicCover.Global R κ n B)) :=
  stratum (fun i => FrozenAcyclicCover.initial R κ n B (Sum.inl i)) I

theorem actual_adjacent_indices (I J : Finset (Fin n))
    {p : PrimeSpectrum (FrozenAcyclicCover.Global R κ n B)}
    (hp : p ∈ closure (actualStratum R κ n B I)) (hq : p ∈ actualStratum R κ n B J)
    (hcard : J.card = I.card + 1) : ∃ i ∉ I, insert i I = J :=
  adjacent_indices _ I J hp hq hcard

theorem actual_nonadjacent_disjoint (I J : Finset (Fin n))
    (hcard : J.card = I.card + 1) (h : ∀ i ∉ I, insert i I ≠ J) :
    closure (actualStratum R κ n B I) ∩ actualStratum R κ n B J = ∅ :=
  nonadjacent_disjoint _ I J hcard h

end Actual
#print axioms stratum
#print axioms closure_zero
#print axioms closure_subset_indices
#print axioms disjoint_of_not_subset
#print axioms adjacent_indices
#print axioms nonadjacent_disjoint
#print axioms actualStratum
#print axioms actual_adjacent_indices
#print axioms actual_nonadjacent_disjoint
end Verification.PrimeStratumIncidence
