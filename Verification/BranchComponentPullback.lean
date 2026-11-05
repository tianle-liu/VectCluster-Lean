/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.BoundaryComponentSelector
import Verification.ProductComponentIdempotents

/-!
# Branch Component Pullback

The order of a component-supported parameter is the pullback of the
component indicator along the actual map on prime spectra. Thus its entry
is 0 or 1 according to geometry, with no free incidence matrix as input.
-/
noncomputable section
namespace Verification.BranchComponentPullback
open Verification.ReducedBoundaryBranchOrder
open Verification.BoundaryComponentSelector Verification.ProductComponentIdempotents
variable {A : Type*} [CommRing A] (x : A)
variable {J : Type*} (D : J → Type*) [∀ j, CommRing (D j)] [∀ j, IsDomain (D j)]
variable (e : (A ⧸ Ideal.span {x}) ≃+* ∀ j, D j) (j : J)

def branchPoint : PrimeSpectrum A := ⟨branch A x D e j, branch_prime A x D e j⟩

variable {S I : Type*} [CommRing S] [Finite I]
variable (C : I → Type*) [∀ i, CommRing (C i)] (E : S ≃+* ∀ i, C i)
variable (f : S →+* A)

def sourcePoint : PrimeSpectrum S := PrimeSpectrum.comap f (branchPoint x D e j)

theorem indicator_nonzero_iff (i : I) :
    projection A x D e j (f (indicator C E i)) ≠ 0 ↔
      sourcePoint x D e j f ∈ Set.range (StratumComponents.componentMap C E i) :=
  pullback_indicator C E f (branchPoint x D e j) i

variable [IsNoetherianRing A] (hx : IsSMulRegular A x)

omit [Finite I] [IsNoetherianRing A] in
theorem parameter_unit_on_open (i : I) :
    IsUnit (algebraMap A (Localization.Away x) (element (f (indicator C E i)) x)) := by
  apply isUnit_on_open
  rw [← map_mul, indicator_idempotent]

theorem order_component_pullback (i : I) :
    order A x D e j hx (element (f (indicator C E i)) x) =
      @ite ℕ∞ (sourcePoint x D e j f ∈ Set.range (StratumComponents.componentMap C E i))
        (Classical.propDecidable _) 1 0 := by
  classical
  by_cases hp : sourcePoint x D e j f ∈ Set.range (StratumComponents.componentMap C E i)
  · rw [if_pos hp]
    apply order_one
    · rw [← map_mul, indicator_idempotent]
    · exact (indicator_nonzero_iff x D e j C E f i).mpr hp
  · rw [if_neg hp]
    apply order_zero
    exact Classical.not_not.mp (fun hn => hp ((indicator_nonzero_iff x D e j C E f i).mp hn))

#print axioms branchPoint
#print axioms sourcePoint
#print axioms indicator_nonzero_iff
#print axioms parameter_unit_on_open
#print axioms order_component_pullback
end Verification.BranchComponentPullback
