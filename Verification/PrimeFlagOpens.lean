/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrimeAdjacentExcision
import Verification.CoordinateFlag

/-!
# Prime Flag Opens

Inside a fixed J-chart, removing all old-coordinate zeros gives the
literal union of the edge charts indexed by coordinates other than v.
The preceding global stage is smaller; its additional components are
precisely those killed by the projection to the chosen adjacent face.
-/
noncomputable section
namespace Verification.PrimeFlagOpens
open CategoryTheory AlgebraicGeometry
open Verification.PrimeCoordinateFiltration Verification.PrimeAdjacentCharts
open Verification.PrimeAdjacentExcision
variable (A V : Type) [CommRing A] [Fintype V] [DecidableEq V]
variable (x : V → A) (J : Finset V) (r : ℕ) (hr : J.card = r+1) (v : J)

def old : (Spec (CommRingCat.of A)).Opens :=
  ⨆ w : CoordinateFlag.Old J v, edgeChart A V x J w.val

include hr in
theorem old_le_current : old A V x J v ≤ current A V x J r :=
  iSup_le (fun w => edgeChart_le_current A V x J r hr w.val)

theorem other_le_old (w : J) (h : w ≠ v) : edgeChart A V x J w ≤ old A V x J v :=
  le_iSup (fun z : CoordinateFlag.Old J v => edgeChart A V x J z.val) ⟨w,h⟩

include hr in
theorem previous_le_old : previous A V x J r ≤ old A V x J v := by
  intro p hp
  have hc := (mem_stage x r p).mp hp.1
  have hs := (mem_openBy x J p).mp hp.2
  change p ∈ (⨆ w : CoordinateFlag.Old J v,edgeChart A V x J w.val :
    (Spec (CommRingCat.of A)).Opens)
  apply TopologicalSpace.Opens.mem_iSup.mpr
  by_contra hn
  have hsub : J.erase v.val ⊆ zeroSet x p := by
    intro i hi
    by_contra hz
    have hiJ := (Finset.mem_erase.mp hi).2
    have hv := (Finset.mem_erase.mp hi).1
    apply hn
    refine ⟨⟨⟨i,hiJ⟩,fun he => hv (congrArg Subtype.val he)⟩,?_⟩
    change p ∈ openBy x (J.erase i)
    apply (mem_openBy x _ p).mpr
    intro z hzm
    exact Finset.mem_erase.mpr ⟨fun he => hz (he ▸ hzm),hs hzm⟩
  have hh := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem v.property,hr] at hh
  omega

include hr in
theorem old_inter_edge : old A V x J v ⊓ edgeChart A V x J v =
    previous A V x J r ⊓ edgeChart A V x J v := by
  apply le_antisymm
  · intro p hp
    obtain ⟨w,hw⟩ := TopologicalSpace.Opens.mem_iSup.mp hp.1
    have h := two_chart_overlap x J w.val v w.property ⟨hw,hp.2⟩
    have he : J.card-1=r := by omega
    exact ⟨⟨by simpa only [he] using h, chart_erase_le x J v hp.2⟩,hp.2⟩
  · exact inf_le_inf_right _ (previous_le_old A V x J r hr v)

include hr in
theorem cover : current A V x J r ≤ old A V x J v ⊔ edgeChart A V x J v := by
  intro p hp
  have hp' : p ∈ ⨆ w : J,edgeChart A V x J w := by
    have he : current A V x J r = ⨆ w : J,edgeChart A V x J w := by
      dsimp only [current,edgeChart]
      rw [← hr,puncture_cover]
    rwa [he] at hp
  obtain ⟨w,hw⟩ := TopologicalSpace.Opens.mem_iSup.mp hp'
  by_cases h : w=v
  · exact Or.inr (h ▸ hw)
  · exact Or.inl (other_le_old A V x J v w h hw)

#print axioms old
#print axioms old_le_current
#print axioms other_le_old
#print axioms previous_le_old
#print axioms old_inter_edge
#print axioms cover
end Verification.PrimeFlagOpens
