/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PolynomialRegularSequence

/-!
# Coordinate Last Regular

A coordinate remains a nonzerodivisor after all other coordinates
are killed, when every repetition-free coordinate sequence is weakly
regular. This is applied to the literal intermediate exchange quotient.
-/
noncomputable section
universe u
namespace Verification.CoordinateLastRegular
open RingTheory.Sequence
variable {A ι : Type u} [CommRing A] [Fintype ι] (x : ι → A) (v : ι)

def otherIdeal : Ideal A := Ideal.span (Set.range (fun i : {i : ι // i ≠ v} => x i.1))

theorem regular_after_others
    (hreg : ∀ l : List ι, l.Nodup → IsWeaklyRegular A (l.map x)) :
    IsSMulRegular (A ⧸ otherIdeal x v) (Ideal.Quotient.mk (otherIdeal x v) (x v)) := by
  classical
  let l := (Finset.univ.erase v).toList
  have hl : l.Nodup := Finset.nodup_toList _
  have hmem : ∀ i, i ∈ l ↔ i ≠ v := by
    intro i
    simp [l]
  have hnodup : (l ++ [v]).Nodup := by
    rw [List.nodup_append]
    refine ⟨hl,by simp,?_⟩
    intro i hi hj
    have hiv : i = v := List.mem_singleton.mp hj
    exact (hmem i).mp hi hiv
  have h := hreg (l ++ [v]) hnodup
  rw [List.map_append,List.map_singleton,isWeaklyRegular_append_iff] at h
  have hlast := (isWeaklyRegular_singleton_iff _ (x v)).mp h.2
  have hideal : Ideal.ofList (l.map x) = otherIdeal x v := by
    apply congrArg Ideal.span
    ext z
    constructor
    · intro hz
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hz
      exact ⟨⟨i,(hmem i).mp hi⟩,rfl⟩
    · rintro ⟨i,rfl⟩
      exact List.mem_map.mpr ⟨i.val,(hmem i.val).mpr i.property,rfl⟩
  rw [Ideal.smul_eq_mul,Ideal.mul_top,hideal] at hlast
  exact hlast

#print axioms otherIdeal
#print axioms regular_after_others
end Verification.CoordinateLastRegular
