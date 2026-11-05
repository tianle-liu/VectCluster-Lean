/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PrimeStratumPresentation
import Verification.PrimeLayerCover

/-!
# Prime Koszul Cover

For a fixed coordinate stratum, the entire relevant filtration
stage is covered by its independent-coordinate chart and opens where
one of its Koszul parameters is a unit. Thus the locally constructed
regular Koszul resolution has exactly the required global support.
-/
noncomputable section
namespace Verification.PrimeKoszulCover
open Verification.PrimeCoordinateFiltration
variable {A V : Type*} [CommRing A] [Fintype V] [DecidableEq V]
variable (x : V → A) (I : Finset V)

theorem zeroSet_eq (p : PrimeSpectrum A) (hp : p∈stage x (I.card+1))
    (hz : ∀ i∈I,x i∈p.asIdeal) : zeroSet x p=I := by
  have hi : I⊆zeroSet x p := fun i hi => (mem_zeroSet x p i).mpr (hz i hi)
  have hc := (mem_stage x (I.card+1) p).mp hp
  exact (Finset.eq_of_subset_of_card_le hi (by omega)).symm

theorem stratum_zeroLocus : PrimeStratumIncidence.stratum x I=
    (stage x (I.card+1) : Set (PrimeSpectrum A)) ∩
      PrimeSpectrum.zeroLocus (Set.range (fun i : I => x i.val)) := by
  ext p
  constructor
  · intro hs
    refine ⟨(mem_stage x (I.card+1) p).mpr ?_,(PrimeSpectrum.mem_zeroLocus p _).mpr ?_⟩
    · rw [(stratum_zeroSet x I p).mp hs]
      exact Nat.lt_succ_self _
    · rintro _ ⟨i,rfl⟩
      exact (hs i.val).mpr i.property
  · rintro ⟨hp,hz⟩
    apply (stratum_zeroSet x I p).mpr
    exact zeroSet_eq x I p hp (fun i hi =>
      (PrimeSpectrum.mem_zeroLocus p _).mp hz (Set.mem_range.mpr ⟨⟨i,hi⟩,rfl⟩))

theorem cover : stage x (I.card+1) ≤ openBy x I ⊔ ⨆ i : I,PrimeSpectrum.basicOpen (x i.val) := by
  intro p hp
  by_cases hz : ∀ i∈I,x i∈p.asIdeal
  · exact Or.inl ((mem_openBy x I p).mpr (by rw [zeroSet_eq x I p hp hz]))
  · push_neg at hz
    obtain ⟨i,hi,hx⟩ := hz
    exact Or.inr (TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i,hi⟩,hx⟩)

theorem closed_support_in_chart (p : PrimeSpectrum A)
    (hp : p∈stage x (I.card+1))
    (hz : p∈PrimeSpectrum.zeroLocus (Set.range (fun i : I => x i.val))) : p∈openBy x I := by
  apply (mem_openBy x I p).mpr
  have he := (stratum_zeroSet x I p).mp ((stratum_zeroLocus x I).symm ▸ ⟨hp,hz⟩)
  rw [he]

omit [Fintype V] [DecidableEq V] in
theorem unit_open_disjoint (i : I) :
    Disjoint (PrimeStratumIncidence.stratum x I)
      (PrimeSpectrum.basicOpen (x i.val) : Set (PrimeSpectrum A)) := by
  apply Set.disjoint_left.mpr
  intro p hs hu
  exact hu ((hs i.val).mpr i.property)

#print axioms zeroSet_eq
#print axioms stratum_zeroLocus
#print axioms cover
#print axioms closed_support_in_chart
#print axioms unit_open_disjoint
end Verification.PrimeKoszulCover
