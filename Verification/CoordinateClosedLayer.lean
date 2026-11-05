/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.CoordinateClosedImmersion

/-!
# Coordinate Closed Layer

The closed components of one global filtration layer, their actual
closed immersions, their disjointness, and their complement. These are
the geometric hypotheses of the usual G-theory localization sequence.
-/
noncomputable section
namespace Verification.CoordinateClosedLayer
open CategoryTheory AlgebraicGeometry
open Verification.PrimeCoordinateFiltration
variable (A V : Type) [CommRing A] [Fintype V] [DecidableEq V]
variable (x : V → A) (Allowed : Finset V → Prop) (r : ℕ)

abbrev Index := PrimeLayerCover.Index Allowed r
abbrev ambient := PrimeSchemeFiltration.stageOpen A x (r+1)

def ambientIso (i : Index V Allowed r) :
    (CoordinateClosedImmersion.ambient A V x i.val).toScheme ≅ (ambient A V x r).toScheme :=
  (Spec (CommRingCat.of A)).isoOfEq (by
    dsimp only [CoordinateClosedImmersion.ambient,ambient]
    rw [i.property.1])

def inclusion (i : Index V Allowed r) : CoordinateClosedImmersion.source A V x i.val ⟶
    (ambient A V x r).toScheme :=
  CoordinateClosedImmersion.inclusion A V x i.val ≫ (ambientIso A V x Allowed r i).hom

instance inclusion_closed (i : Index V Allowed r) : IsClosedImmersion (inclusion A V x Allowed r i) := by
  unfold inclusion
  infer_instance

theorem inclusion_fac (i : Index V Allowed r) :
    inclusion A V x Allowed r i ≫ (ambient A V x r).ι =
      CoordinateClosedImmersion.globalMap A V x i.val := by
  simp only [inclusion,Category.assoc,ambientIso,Scheme.isoOfEq_hom_ι,
    CoordinateClosedImmersion.inclusion_fac]

theorem range_inclusion (i : Index V Allowed r) :
    Set.range (inclusion A V x Allowed r i).base =
      (ambient A V x r).ι.base ⁻¹' PrimeStratumIncidence.stratum x i.val := by
  have hf (z : CoordinateClosedImmersion.source A V x i.val) :
      (ambient A V x r).ι.base ((inclusion A V x Allowed r i).base z) =
        (CoordinateClosedImmersion.globalMap A V x i.val).base z :=
    congrArg (fun f => f.base z) (inclusion_fac A V x Allowed r i)
  ext p
  constructor
  · rintro ⟨z,rfl⟩
    change (ambient A V x r).ι.base ((inclusion A V x Allowed r i).base z) ∈
      PrimeStratumIncidence.stratum x i.val
    rw [hf,← CoordinateClosedImmersion.range_globalMap A V x i.val]
    exact ⟨z,rfl⟩
  · intro hp
    change (ambient A V x r).ι.base p ∈ PrimeStratumIncidence.stratum x i.val at hp
    rw [← CoordinateClosedImmersion.range_globalMap A V x i.val] at hp
    obtain ⟨z,hz⟩ := hp
    exact ⟨z,(ambient A V x r).ι.isOpenEmbedding.injective ((hf z).trans hz)⟩

theorem disjoint (i j : Index V Allowed r) (hij : i≠j) :
    Disjoint (Set.range (inclusion A V x Allowed r i).base)
      (Set.range (inclusion A V x Allowed r j).base) := by
  rw [range_inclusion,range_inclusion]
  apply Set.disjoint_left.mpr
  intro p hi hj
  apply hij
  apply Subtype.ext
  exact ((stratum_zeroSet x i.val _).mp hi).symm.trans ((stratum_zeroSet x j.val _).mp hj)

def previous : (ambient A V x r).toScheme.Opens :=
  (ambient A V x r).ι ⁻¹ᵁ PrimeSchemeFiltration.stageOpen A x r

theorem complement (hall : ∀ p : PrimeSpectrum A, Allowed (zeroSet x p)) :
    (⋃ i : Index V Allowed r,Set.range (inclusion A V x Allowed r i).base) =
      (previous A V x r : Set (ambient A V x r).toScheme)ᶜ := by
  ext p
  simp only [Set.mem_iUnion,Set.mem_compl_iff]
  have hp : (ambient A V x r).ι.base p ∈ stage x (r+1) := by
    have hh : (ambient A V x r).ι.base p ∈ Set.range (ambient A V x r).ι.base := ⟨p,rfl⟩
    rw [Scheme.Opens.range_ι] at hh
    exact hh
  change (∃ i : Index V Allowed r,p∈Set.range (inclusion A V x Allowed r i).base) ↔
    ¬(ambient A V x r).ι.base p∈stage x r
  constructor
  · rintro ⟨i,hi⟩ hn
    rw [range_inclusion] at hi
    have he := (stratum_zeroSet x i.val _).mp hi
    have hc := (mem_stage x r _).mp hn
    rw [he,i.property.1] at hc
    exact (Nat.lt_irrefl r) hc
  · intro hn
    have hc : (zeroSet x ((ambient A V x r).ι.base p)).card=r := by
      have ha := (mem_stage x (r+1) _).mp hp
      have hb := (mem_stage x r _).not.mp hn
      omega
    let i : Index V Allowed r := ⟨zeroSet x ((ambient A V x r).ι.base p),hc,hall _⟩
    refine ⟨i,?_⟩
    rw [range_inclusion]
    exact (stratum_zeroSet x i.val _).mpr rfl

#print axioms Index
#print axioms ambient
#print axioms ambientIso
#print axioms inclusion
#print axioms inclusion_closed
#print axioms inclusion_fac
#print axioms range_inclusion
#print axioms disjoint
#print axioms previous
#print axioms complement
end Verification.CoordinateClosedLayer
