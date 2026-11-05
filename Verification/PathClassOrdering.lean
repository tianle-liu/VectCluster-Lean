/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathClassRepresentatives
import Mathlib.Order.Hom.Set
import Mathlib.Data.Fintype.EquivFin

/-!
# Path Class Ordering

The natural order on the actual surviving path classes is their counting
coordinate. In particular the new face is exactly the three consecutive
positions prescribed by faceIndex, even after repeated neighbor merges.
-/
noncomputable section
namespace Verification.PathClassOrdering
open Finset Verification.PathCompression Verification.PathClassRepresentatives

theorem available_succ_deleted (I : Finset ℕ) (p : ℕ) (hp : p ∈ deleted I) :
    available I (p+1)=available I p := by
  ext k
  simp only [available,mem_sdiff,mem_range]
  by_cases he : k=p
  · subst k
    simp only [hp,not_true_eq_false,and_false]
  · have hh : k<p+1 ↔ k<p := by omega
    rw [hh]

theorem available_succ_free (I : Finset ℕ) (p : ℕ) (hp : p ∉ deleted I) :
    available I (p+1)=insert p (available I p) := by
  ext k
  simp only [available,mem_sdiff,mem_range,mem_insert]
  by_cases he : k=p
  · subst k
    simp only [hp,not_false_eq_true,and_true,Nat.lt_succ_self,true_or]
  · have hh : k<p+1 ↔ k<p := by omega
    rw [hh]
    simp only [he,false_or]

theorem coordinate_succ_deleted (I : Finset ℕ) (p : ℕ) (hp : p ∈ deleted I) :
    coordinate I (p+1)=coordinate I p := by
  unfold coordinate
  rw [available_succ_deleted I p hp]

theorem coordinate_succ_free (I : Finset ℕ) (p : ℕ) (hp : p ∉ deleted I) :
    coordinate I (p+1)=coordinate I p+1 := by
  unfold coordinate
  rw [available_succ_free I p hp,card_insert_of_not_mem]
  simp [available]

theorem coordinate_representative (I : Finset ℕ) (p : ℕ) :
    coordinate I (representative I p+1)=coordinate I (p+1) := by
  induction p using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more p ih _ =>
    rw [representative]
    split_ifs with hp
    · have h₁ : p+1 ∈ deleted I := mem_union_left _ hp
      have h₂ : p+2 ∈ deleted I := mem_union_right _ (mem_image.mpr ⟨p+1,hp,rfl⟩)
      rw [coordinate_succ_deleted I (p+2) h₂,coordinate_succ_deleted I (p+1) h₁]
      exact ih
    · rfl

variable {n : ℕ} {I : Finset ℕ}

instance representativesLinearOrder : LinearOrder (Representatives n I) :=
  inferInstanceAs (LinearOrder ↥(available I (n+2)))

def index (p : Representatives n I) : Fin (available I (n+2)).card :=
  ⟨coordinate I p.val,by
    have hc := coordinate_succ_free I p.val (mem_sdiff.mp p.property).2
    have hp := mem_range.mp (mem_sdiff.mp p.property).1
    have hle := card_le_card (available_mono I (by omega : p.val+1 ≤ n+2))
    unfold coordinate at hc ⊢
    omega⟩

theorem index_strictMono : StrictMono (index (n:=n) (I:=I)) := by
  intro p q hpq
  change coordinate I p.val < coordinate I q.val
  have hc := coordinate_succ_free I p.val (mem_sdiff.mp p.property).2
  have hle := card_le_card (available_mono I (by change p.val<q.val at hpq;omega : p.val+1 ≤ q.val))
  unfold coordinate at *
  omega

theorem index_bijective : Function.Bijective (index (n:=n) (I:=I)) := by
  have hc : Fintype.card (Representatives n I)=Fintype.card (Fin (available I (n+2)).card) := by
    rw [Fintype.card_fin]
    exact Fintype.card_coe _
  exact (Fintype.bijective_iff_injective_and_card index).mpr ⟨index_strictMono.injective,hc⟩

def orderIso : Representatives n I ≃o Fin (available I (n+2)).card :=
  StrictMono.orderIsoOfSurjective index index_strictMono index_bijective.2

theorem index_compress (hI : Admissible n I) (p : Vertices n I) :
    (index (compress hI p)).val+1=coordinate I (p.val+1) := by
  have hr := representative_available hI (mem_range.mp (mem_sdiff.mp p.property).1) (mem_sdiff.mp p.property).2
  have hc := coordinate_succ_free I (representative I p.val) (mem_sdiff.mp hr).2
  change coordinate I (representative I p.val)+1=coordinate I (p.val+1)
  rw [← hc,coordinate_representative]

theorem index_normal (hI : Admissible n I) (j : ℕ) (hj : j ∈ Icc 1 n) (ha : Addable I j)
    (p : Vertices n I) (hp : p.val=j) : (index (compress hI p)).val=faceIndex I j+1 := by
  have hc := index_compress hI p
  rw [hp,coordinate_succ_free I j ha.1] at hc
  have hpos := coordinate_positive hI (mem_Icc.mp hj).1
  unfold faceIndex
  omega

theorem index_left (hI : Admissible n I) (j : ℕ) (hj : j ∈ Icc 1 n)
    (p : Vertices n I) (hp : p.val=j-1) : (index (compress hI p)).val=faceIndex I j := by
  have hc := index_compress hI p
  have hjp := (mem_Icc.mp hj).1
  have he : j-1+1=j := by omega
  rw [hp,he] at hc
  unfold faceIndex
  omega

theorem index_right (hI : Admissible n I) (j : ℕ) (hj : j ∈ Icc 1 n) (ha : Addable I j)
    (p : Vertices n I) (hp : p.val=j+1) : (index (compress hI p)).val=faceIndex I j+2 := by
  have hc := index_compress hI p
  rw [hp,coordinate_succ_free I (j+1) ha.2,coordinate_succ_free I j ha.1] at hc
  have hpos := coordinate_positive hI (mem_Icc.mp hj).1
  unfold faceIndex
  omega

#print axioms available_succ_deleted
#print axioms available_succ_free
#print axioms coordinate_succ_deleted
#print axioms coordinate_succ_free
#print axioms coordinate_representative
#print axioms representativesLinearOrder
#print axioms index
#print axioms index_strictMono
#print axioms index_bijective
#print axioms orderIso
#print axioms index_compress
#print axioms index_normal
#print axioms index_left
#print axioms index_right
end Verification.PathClassOrdering
