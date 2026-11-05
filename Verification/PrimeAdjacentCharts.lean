/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrimeCoordinateFiltration

/-!
# Prime Adjacent Charts

The actual adjacent coordinate charts inside a fixed chart. These open
identities express the local codimension-one incidences of the global
filtration using the original coordinates and their prime ideals.
-/
noncomputable section
namespace Verification.PrimeAdjacentCharts
open Verification.PrimeCoordinateFiltration
variable {A V : Type*} [CommRing A] [Fintype V] [DecidableEq V]
variable (x : V → A) (J : Finset V)

theorem chart_erase (v : J) : openBy x (J.erase v.val) = openBy x J ⊓ PrimeSpectrum.basicOpen (x v.val) := by
  ext p
  change p ∈ openBy x (J.erase v.val) ↔ p ∈ openBy x J ∧ x v.val ∉ p.asIdeal
  rw [mem_openBy,mem_openBy]
  constructor
  · intro h
    refine ⟨fun i hi => (Finset.mem_erase.mp (h hi)).2,?_⟩
    intro hx
    exact (Finset.mem_erase.mp (h ((mem_zeroSet x p v.val).mpr hx))).1 rfl
  · rintro ⟨h,hn⟩ i hi
    apply Finset.mem_erase.mpr
    refine ⟨?_,h hi⟩
    intro heq
    subst i
    exact hn ((mem_zeroSet x p v.val).mp hi)

theorem chart_erase_le (v : J) : openBy x (J.erase v.val) ≤ openBy x J := by
  rw [chart_erase]
  exact inf_le_left

theorem puncture_cover : stage x J.card ⊓ openBy x J = ⨆ v : J,openBy x (J.erase v.val) := by
  ext p
  change (p ∈ stage x J.card ∧ p ∈ openBy x J) ↔ _
  rw [mem_stage,mem_openBy]
  change ((zeroSet x p).card < J.card ∧ zeroSet x p ⊆ J) ↔
    p ∈ (⨆ v : J,openBy x (J.erase v.val) : TopologicalSpace.Opens (PrimeSpectrum A))
  rw [TopologicalSpace.Opens.mem_iSup]
  constructor
  · rintro ⟨hc,hs⟩
    have hne : zeroSet x p ≠ J := fun h => (Nat.lt_irrefl J.card) (h ▸ hc)
    obtain ⟨v,hv,hn⟩ := Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hs,hne⟩)
    refine ⟨⟨v,hv⟩,?_⟩
    rw [chart_erase]
    exact ⟨(mem_openBy x J p).mpr hs,fun h => hn ((mem_zeroSet x p v).mpr h)⟩
  · rintro ⟨v,hv⟩
    have hs := (mem_openBy x (J.erase v.val) p).mp hv
    refine ⟨?_,hs.trans (Finset.erase_subset _ _)⟩
    have hc := Finset.card_le_card hs
    have hj := Finset.card_erase_of_mem v.property
    have hp := Finset.card_pos.mpr ⟨v.val,v.property⟩
    omega

theorem two_chart_overlap (v w : J) (hvw : v ≠ w) :
    openBy x (J.erase v.val) ⊓ openBy x (J.erase w.val) ≤ stage x (J.card-1) := by
  intro p hp
  apply (mem_stage x (J.card-1) p).mpr
  have hv := (mem_openBy x (J.erase v.val) p).mp hp.1
  have hw := (mem_openBy x (J.erase w.val) p).mp hp.2
  have hsub : zeroSet x p ⊆ (J.erase v.val).erase w.val := by
    intro i hi
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp (hw hi)).1,hv hi⟩
  have hwmem : w.val ∈ J.erase v.val :=
    Finset.mem_erase.mpr ⟨fun h => hvw (Subtype.ext h.symm),w.property⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hwmem,Finset.card_erase_of_mem v.property] at hc
  have hp' := Finset.card_pos.mpr ⟨w.val,hwmem⟩
  rw [Finset.card_erase_of_mem v.property] at hp'
  omega

#print axioms chart_erase
#print axioms chart_erase_le
#print axioms puncture_cover
#print axioms two_chart_overlap
end Verification.PrimeAdjacentCharts
