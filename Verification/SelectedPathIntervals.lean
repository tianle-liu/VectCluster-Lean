/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.Order.Interval.Set.OrdConnectedComponent
import Mathlib.Order.Cover
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Finset.Sort
import Verification.PathOrientationSigns

/-!
# Selected Path Intervals

An arbitrary selected subset of a finite path is partitioned into its
actual consecutive intervals. The increasing coordinates preserve adjacency.
-/
noncomputable section
namespace Verification.SelectedPathIntervals
open Classical Set
variable {n : ℕ} (K : Set (Fin n))
abbrev Component := ↥(Set.ordConnectedSection K)
abbrev Points (c : Component K) := ↥(Set.ordConnectedComponent K c.val)
instance componentsFintype : Fintype (Component K) := Fintype.ofFinite _
instance pointsFintype (c : Component K) : Fintype (Points K c) := Fintype.ofFinite _

def join : (Σc : Component K,Points K c)→K :=
  fun x=>⟨x.2.val,Set.ordConnectedComponent_subset x.2.property⟩

theorem component_eq {c d : Component K} {x : Fin n}
    (hx : x∈Set.ordConnectedComponent K c.val)
    (hy : x∈Set.ordConnectedComponent K d.val) : c=d := by
  apply Subtype.ext
  exact Set.eq_of_mem_ordConnectedSection_of_uIcc_subset c.property d.property
    (Set.mem_ordConnectedComponent_trans hx (Set.mem_ordConnectedComponent_comm.mp hy))

def split : (Σc : Component K,Points K c)≃K := Equiv.ofBijective (join K) (by
  constructor
  · rintro ⟨c,x⟩ ⟨d,y⟩ h
    have hxy : x.val=y.val := congrArg Subtype.val h
    have hcd : c=d := component_eq K x.property (hxy.symm ▸ y.property)
    subst d
    have he : x=y := Subtype.ext hxy
    cases he
    rfl
  · intro x
    refine ⟨⟨⟨Set.ordConnectedProj K x,⟨x,rfl⟩⟩,⟨x.val,?_⟩⟩,rfl⟩
    exact Set.mem_ordConnectedComponent_ordConnectedProj K x)

theorem split_apply (c : Component K) (x : Points K c) : (split K ⟨c,x⟩).val=x.val := rfl

def ordering (c : Component K) : Fin (Fintype.card (Points K c))≃oPoints K c :=
  Fintype.orderIsoFinOfCardEq (Points K c) rfl

theorem natural_covby (x y : ℕ) : x ⋖ y ↔ x+1=y := by
  constructor
  · intro h
    have hlt := h.1
    have hn := h.2 (c:=x+1) (by omega)
    omega
  · rintro rfl
    constructor
    · omega
    · intro z hx hz
      omega

theorem consecutive (c : Component K) (i j : Fin (Fintype.card (Points K c))) :
    (ordering K c j).val.val=(ordering K c i).val.val+1 ↔ j.val=i.val+1 := by
  have hconv : (Set.range (OrderEmbedding.subtype (Set.ordConnectedComponent K c.val))).OrdConnected := by
    change (Set.range ((↑) : Points K c→Fin n)).OrdConnected
    rw [Subtype.range_coe]
    infer_instance
  have hh := Set.OrdConnected.apply_covBy_apply_iff
    (OrderEmbedding.subtype (Set.ordConnectedComponent K c.val)) hconv
    (a:=ordering K c i) (b:=ordering K c j)
  rw [apply_covBy_apply_iff] at hh
  change ((ordering K c i).val ⋖ (ordering K c j).val) ↔ (i ⋖ j) at hh
  rw [←Fin.coe_covBy_iff,←Fin.coe_covBy_iff] at hh
  simpa only [natural_covby,eq_comm] using hh

theorem component_eq_of_consecutive {c d : Component K} (x : Points K c) (y : Points K d)
    (h : y.val.val=x.val.val+1) : c=d := by
  have hxy : y.val∈Set.ordConnectedComponent K x.val := by
    change Set.uIcc x.val y.val⊆K
    intro z hz
    have hz' := Set.mem_uIcc.mp hz
    have he : z=x.val ∨ z=y.val := by
      have hh : (x.val.val≤z.val ∧ z.val≤y.val.val) ∨ (y.val.val≤z.val ∧ z.val≤x.val.val) := hz'
      rcases (show z.val=x.val.val ∨ z.val=y.val.val by omega) with h|h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    rcases he with rfl|rfl
    · exact Set.ordConnectedComponent_subset x.property
    · exact Set.ordConnectedComponent_subset y.property
  exact component_eq K (Set.mem_ordConnectedComponent_trans x.property hxy) y.property

#print axioms Component
#print axioms Points
#print axioms componentsFintype
#print axioms pointsFintype
#print axioms join
#print axioms component_eq
#print axioms split
#print axioms split_apply
#print axioms ordering
#print axioms natural_covby
#print axioms consecutive
#print axioms component_eq_of_consecutive
end Verification.SelectedPathIntervals
