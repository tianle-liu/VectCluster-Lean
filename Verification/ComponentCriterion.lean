/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Component Criterion

The minimal-disconnected-stratum argument of manuscript.tex:1887–1899,
for actual component-function pullback maps on a downward-closed family.
-/

namespace Verification.ComponentCriterion

open Finset
variable {α : Type*} [DecidableEq α]
variable (P : Finset α → Type*)
variable (res : ∀ S : Finset α, ∀ i : S, P S → P (S.erase i.val))

noncomputable def jointPullback (S : Finset α) :
    (∀ i : S, P (S.erase i.val) → ℤ) →ₗ[ℤ] (P S → ℤ) where
  toFun x c := ∑ i : S, x i (res S i c)
  map_add' x y := by ext c; simp [Finset.sum_add_distrib]
  map_smul' r x := by ext c; simp [Finset.mul_sum]

theorem singleton_predecessors_force_singleton (S : Finset α)
    (hpre : ∀ i : S, Subsingleton (P (S.erase i.val)))
    (hsurj : Function.Surjective (jointPullback P res S)) : Subsingleton (P S) := by
  classical
  constructor
  intro a b
  by_contra hab
  obtain ⟨x, hx⟩ := hsurj (fun c => if c = a then 1 else 0)
  have hconst : jointPullback P res S x a = jointPullback P res S x b := by
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (x i) ((hpre i).elim (res S i a) (res S i b))
  rw [hx] at hconst
  have hba : b ≠ a := Ne.symm hab
  simp [hba] at hconst

theorem singleton_target_surjective (S : Finset α) (hS : S.Nonempty)
    [Nonempty (P S)] [Subsingleton (P S)] :
    Function.Surjective (jointPullback P res S) := by
  classical
  obtain ⟨i, hi⟩ := hS
  let i₀ : S := ⟨i, hi⟩
  obtain ⟨a⟩ := ‹Nonempty (P S)›
  intro f
  refine ⟨fun j _ => if j = i₀ then f a else 0, ?_⟩
  ext c
  change (∑ j : S, if j = i₀ then f a else 0) = f c
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact congrArg f (Subsingleton.elim a c)

/-- A simultaneous criterion on every simplex of an arbitrary downward-closed
family, not only the example graph in the manuscript. -/
theorem all_component_maps_surjective_iff
    (F : Set (Finset α))
    (hdown : ∀ S ∈ F, ∀ T, T ⊆ S → T ∈ F)
    (hbase : Subsingleton (P ∅))
    (hne : ∀ S ∈ F, Nonempty (P S)) :
    (∀ S ∈ F, S.Nonempty → Function.Surjective (jointPullback P res S)) ↔
      ∀ S ∈ F, Subsingleton (P S) := by
  constructor
  · intro hall S
    refine Finset.strongInductionOn S ?_
    intro S ih hSF
    by_cases hS : S = ∅
    · simpa [hS] using hbase
    · apply singleton_predecessors_force_singleton P res S
      · intro i
        exact ih (S.erase i.val) (Finset.erase_ssubset i.property)
          (hdown S hSF _ (Finset.erase_subset _ _))
      · exact hall S hSF (Finset.nonempty_iff_ne_empty.mpr hS)
  · intro hall S hSF hS
    letI : Subsingleton (P S) := hall S hSF
    letI : Nonempty (P S) := hne S hSF
    exact singleton_target_surjective P res S hS

/-- The actual component-function cokernel in the Chow criterion. -/
abbrev ComponentCokernel (S : Finset α) :=
  (P S → ℤ) ⧸ LinearMap.range (jointPullback P res S)

theorem component_cokernel_vanishes_iff (S : Finset α) :
    Subsingleton (ComponentCokernel P res S) ↔
      Function.Surjective (jointPullback P res S) := by
  rw [Submodule.subsingleton_quotient_iff_eq_top, LinearMap.range_eq_top]

/-- This criterion speaks about genuine quotient groups, not only matrices. -/
theorem all_component_cokernels_vanish_iff
    (F : Set (Finset α))
    (hdown : ∀ S ∈ F, ∀ T, T ⊆ S → T ∈ F)
    (hbase : Subsingleton (P ∅))
    (hne : ∀ S ∈ F, Nonempty (P S)) :
    (∀ S ∈ F, S.Nonempty → Subsingleton (ComponentCokernel P res S)) ↔
      ∀ S ∈ F, Subsingleton (P S) := by
  simp only [component_cokernel_vanishes_iff]
  exact all_component_maps_surjective_iff P res F hdown hbase hne

#print axioms component_cokernel_vanishes_iff
#print axioms all_component_cokernels_vanish_iff
#print axioms singleton_predecessors_force_singleton
#print axioms singleton_target_surjective
#print axioms all_component_maps_surjective_iff

end Verification.ComponentCriterion

-- Explicit dependency audit of the early module constructions.
#print axioms Verification.ComponentCriterion.ComponentCokernel
#print axioms Verification.ComponentCriterion.jointPullback
