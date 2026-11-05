/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.StratumComponents

/-!
# Product Component Idempotents

The idempotent of a product factor cuts out its actual connected
component. Pulling it back along a ring map detects the component containing
the image of a point, rather than a freely specified component function.
-/
noncomputable section
namespace Verification.ProductComponentIdempotents
variable {S I : Type*} [CommRing S]
variable (C : I → Type*) [∀ i, CommRing (C i)] (E : S ≃+* ∀ i, C i)

def indicator (i : I) : S := by
  classical
  exact E.symm (Pi.single i 1)

theorem image_indicator (i : I) : E (indicator C E i) =
    (by classical exact Pi.single i 1) :=
  E.apply_symm_apply _

theorem indicator_idempotent (i : I) : indicator C E i * indicator C E i =
    indicator C E i := by
  classical
  apply E.injective
  rw [map_mul, image_indicator]
  funext j
  by_cases h : j = i
  · subst j
    simp
  · simp [Pi.single_apply, h]

theorem indicator_eval_self (i : I) : E (indicator C E i) i = 1 := by
  classical
  rw [image_indicator]
  simp

theorem indicator_eval_other {i j : I} (h : j ≠ i) : E (indicator C E i) j = 0 := by
  classical
  rw [image_indicator]
  simp [Pi.single_apply, h]

variable [Finite I]

theorem not_mem_iff_component (i : I) (p : PrimeSpectrum S) :
    indicator C E i ∉ p.asIdeal ↔
      p ∈ Set.range (StratumComponents.componentMap C E i) := by
  classical
  constructor
  · intro hp
    have hc := Set.eq_univ_iff_forall.mp (StratumComponents.componentMap_cover C E) p
    obtain ⟨j, q, hq⟩ := Set.mem_iUnion.mp hc
    by_cases h : j = i
    · subst j
      exact ⟨q, hq⟩
    · exfalso
      apply hp
      rw [← hq]
      change E (indicator C E i) j ∈ q.asIdeal
      rw [indicator_eval_other C E h]
      exact q.asIdeal.zero_mem
  · rintro ⟨q, rfl⟩ hp
    change E (indicator C E i) i ∈ q.asIdeal at hp
    rw [indicator_eval_self] at hp
    exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hp isUnit_one)

theorem basicOpen_component (i : I) :
    (PrimeSpectrum.basicOpen (indicator C E i) : Set (PrimeSpectrum S)) =
      Set.range (StratumComponents.componentMap C E i) := by
  ext p
  exact not_mem_iff_component C E i p

variable {A : Type*} [CommRing A]

theorem pullback_indicator (f : S →+* A) (p : PrimeSpectrum A) (i : I) :
    f (indicator C E i) ∉ p.asIdeal ↔
      PrimeSpectrum.comap f p ∈ Set.range (StratumComponents.componentMap C E i) :=
  not_mem_iff_component C E i (PrimeSpectrum.comap f p)

#print axioms indicator
#print axioms image_indicator
#print axioms indicator_idempotent
#print axioms indicator_eval_self
#print axioms indicator_eval_other
#print axioms not_mem_iff_component
#print axioms basicOpen_component
#print axioms pullback_indicator
end Verification.ProductComponentIdempotents
