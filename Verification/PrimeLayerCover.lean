/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrimeCoordinateFiltration

/-!
# Prime Layer Cover

The actual finite open cover used for excision of one Zariski layer.
Different coordinate charts in the same layer intersect only in the
preceding filtration stage. These conditions are proved from the original
zero-coordinate sets, not postulated as a cellular decomposition.
-/
noncomputable section
namespace Verification.PrimeLayerCover
open Verification.PrimeCoordinateFiltration
variable {A V : Type*} [CommRing A] [Fintype V] [DecidableEq V]
variable (x : V → A) (Allowed : Finset V → Prop) (r : ℕ)

abbrev Index := {I : Finset V // I.card = r ∧ Allowed I}

instance indexFinite : Finite (Index Allowed r) := inferInstanceAs (Finite {I : Finset V // I.card = r ∧ Allowed I})

def chart (i : Index Allowed r) := openBy x i.val

theorem chart_le_stage (i : Index Allowed r) : chart x Allowed r i ≤ stage x (r+1) := by
  intro p hp
  apply (mem_stage x (r+1) p).mpr
  have h := Finset.card_le_card ((mem_openBy x i.val p).mp hp)
  rw [i.property.1] at h
  omega

theorem cover (hall : ∀ p : PrimeSpectrum A, Allowed (zeroSet x p)) :
    stage x (r+1) ≤ stage x r ⊔ ⨆ i : Index Allowed r, chart x Allowed r i := by
  intro p hp
  by_cases h : (zeroSet x p).card < r
  · exact Or.inl ((mem_stage x r p).mpr h)
  · apply Or.inr
    apply TopologicalSpace.Opens.mem_iSup.mpr
    have hc : (zeroSet x p).card = r := by
      have hp' := (mem_stage x (r+1) p).mp hp
      omega
    exact ⟨⟨zeroSet x p,hc,hall p⟩,(mem_openBy x _ p).mpr (Finset.Subset.refl _)⟩

theorem overlap (i j : Index Allowed r) (hij : i ≠ j) :
    chart x Allowed r i ⊓ chart x Allowed r j ≤ stage x r := by
  intro p hp
  apply (mem_stage x r p).mpr
  have hi := (mem_openBy x i.val p).mp hp.1
  have hj := (mem_openBy x j.val p).mp hp.2
  by_contra h
  have hcard : r ≤ (zeroSet x p).card := Nat.le_of_not_gt h
  have ei := Finset.eq_of_subset_of_card_le hi (by simpa only [i.property.1] using hcard)
  have ej := Finset.eq_of_subset_of_card_le hj (by simpa only [j.property.1] using hcard)
  exact hij (Subtype.ext (ei.symm.trans ej))

theorem local_layer (i : Index Allowed r) :
    (chart x Allowed r i : Set (PrimeSpectrum A)) \ stage x r =
      PrimeStratumIncidence.stratum x i.val := by
  ext p
  change (p ∈ openBy x i.val ∧ ¬p ∈ stage x r) ↔ _
  rw [mem_openBy,mem_stage,stratum_zeroSet]
  constructor
  · rintro ⟨hi,hn⟩
    exact Finset.eq_of_subset_of_card_le hi (by rw [i.property.1]; exact Nat.le_of_not_gt hn)
  · intro he
    rw [he,i.property.1]
    exact ⟨Finset.Subset.refl _,Nat.lt_irrefl _⟩

#print axioms Index
#print axioms indexFinite
#print axioms chart
#print axioms chart_le_stage
#print axioms cover
#print axioms overlap
#print axioms local_layer
end Verification.PrimeLayerCover
