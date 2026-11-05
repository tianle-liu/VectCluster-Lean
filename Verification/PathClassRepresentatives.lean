/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathCompression

/-!
# Path Class Representatives

Literal representatives of the coordinate classes obtained by setting
independent path vertices to zero. The right neighbor is repeatedly merged
into its left neighbor; the surviving representatives are exactly available.
-/
namespace Verification.PathClassRepresentatives
open Finset Verification.PathCompression

def representative (I : Finset ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | p+2 => if p+1 ∈ I then representative I p else p+2

theorem representative_le (I : Finset ℕ) (p : ℕ) : representative I p ≤ p := by
  induction p using Nat.twoStepInduction with
  | zero => simp [representative]
  | one => simp [representative]
  | more p ih _ =>
    simp only [representative]
    split_ifs <;> omega

theorem representative_fixed (I : Finset ℕ) {p : ℕ} (hp : p ∉ deleted I) :
    representative I p=p := by
  cases p with
  | zero => rfl
  | succ p =>
    cases p with
    | zero => rfl
    | succ p =>
      rw [representative,if_neg]
      intro hm
      exact hp (mem_union_right _ (mem_image.mpr ⟨p+1,hm,rfl⟩))

theorem representative_merge (I : Finset ℕ) {i : ℕ} (hi : 0<i) (hm : i ∈ I) :
    representative I (i+1)=representative I (i-1) := by
  obtain ⟨p,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i≠0)
  simp only [Nat.succ_sub_one,representative,if_pos hm]

variable {n : ℕ} {I : Finset ℕ}

theorem representative_available (hI : Admissible n I) {p : ℕ}
    (hp : p<n+2) (hn : p ∉ I) : representative I p ∈ available I (n+2) := by
  induction p using Nat.twoStepInduction with
  | zero => exact zero_available hI (by omega)
  | one =>
    change 1 ∈ available I (n+2)
    refine mem_sdiff.mpr ⟨mem_range.mpr hp,?_⟩
    rintro hm
    rcases mem_union.mp hm with hm | hm
    · exact hn hm
    · obtain ⟨j,hj,he⟩ := mem_image.mp hm
      have hh := mem_Icc.mp (hI.1 hj)
      omega
  | more p ih _ =>
    rw [representative]
    split_ifs with hm
    · apply ih (by omega)
      intro hpI
      exact hI.2 p hpI hm
    · refine mem_sdiff.mpr ⟨mem_range.mpr hp,?_⟩
      rintro hd
      rcases mem_union.mp hd with hd | hd
      · exact hn hd
      · obtain ⟨j,hj,he⟩ := mem_image.mp hd
        have hjp : j=p+1 := by omega
        exact hm (hjp ▸ hj)

theorem representative_evaluate {A : Type*} (f : ℕ → A)
    (h : ∀ i ∈ I, f (i+1)=f (i-1)) (p : ℕ) :
    f (representative I p)=f p := by
  induction p using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more p ih _ =>
    rw [representative]
    split_ifs with hm
    · exact ih.trans (by simpa only [Nat.add_sub_cancel] using (h (p+1) hm).symm)
    · rfl

def Vertices (n : ℕ) (I : Finset ℕ) := ↥(range (n+2) \ I)
def Representatives (n : ℕ) (I : Finset ℕ) := ↥(available I (n+2))

instance verticesFintype : Fintype (Vertices n I) := inferInstanceAs (Fintype ↥(range (n+2) \ I))
instance representativesFintype : Fintype (Representatives n I) := inferInstanceAs (Fintype ↥(available I (n+2)))

def compress (hI : Admissible n I) (p : Vertices n I) : Representatives n I :=
  ⟨representative I p.val,representative_available hI
    (mem_range.mp (mem_sdiff.mp p.property).1) (mem_sdiff.mp p.property).2⟩

def includeRepresentative (p : Representatives n I) : Vertices n I :=
  ⟨p.val,mem_sdiff.mpr ⟨(mem_sdiff.mp p.property).1,
    fun hm => (mem_sdiff.mp p.property).2 (mem_union_left _ hm)⟩⟩

theorem compress_include (hI : Admissible n I) (p : Representatives n I) :
    compress hI (includeRepresentative p)=p := by
  apply Subtype.ext
  exact representative_fixed I (mem_sdiff.mp p.property).2

def leftVertex (hI : Admissible n I) (i : I) : Vertices n I :=
  ⟨i.val-1,mem_sdiff.mpr ⟨mem_range.mpr (by have hh:=mem_Icc.mp (hI.1 i.property);omega),by
    intro hm
    have hh:=mem_Icc.mp (hI.1 i.property)
    have he : i.val-1+1=i.val := by omega
    exact hI.2 (i.val-1) hm (he ▸ i.property)⟩⟩

def rightVertex (hI : Admissible n I) (i : I) : Vertices n I :=
  ⟨i.val+1,mem_sdiff.mpr ⟨mem_range.mpr (by have hh:=mem_Icc.mp (hI.1 i.property);omega),
    hI.2 i.val i.property⟩⟩

theorem compress_neighbors (hI : Admissible n I) (i : I) :
    compress hI (rightVertex hI i)=compress hI (leftVertex hI i) := by
  apply Subtype.ext
  exact representative_merge I (mem_Icc.mp (hI.1 i.property)).1 i.property


/-- Values satisfying precisely the zero-vertex neighbor relations are
recovered from the canonical surviving representatives. -/
theorem vertex_evaluate {A : Type*} (hI : Admissible n I) (f : Vertices n I → A)
    (h : ∀ i : I, f (rightVertex hI i)=f (leftVertex hI i)) (p : Vertices n I) :
    f (includeRepresentative (compress hI p))=f p := by
  classical
  let p₀ : Vertices n I := includeRepresentative ⟨0,zero_available hI (by omega)⟩
  let F : ℕ → A := fun q => if hq : q ∈ range (n+2) \ I then f ⟨q,hq⟩ else f p₀
  have hF : ∀ i ∈ I, F (i+1)=F (i-1) := by
    intro i hi
    have hr : i+1 ∈ range (n+2) \ I := (rightVertex hI ⟨i,hi⟩).property
    have hl : i-1 ∈ range (n+2) \ I := (leftVertex hI ⟨i,hi⟩).property
    dsimp only [F]
    rw [dif_pos hr,dif_pos hl]
    exact h ⟨i,hi⟩
  have hh := representative_evaluate F hF p.val
  have hr : representative I p.val ∈ range (n+2) \ I := (includeRepresentative (compress hI p)).property
  dsimp only [F] at hh
  rw [dif_pos hr,dif_pos p.property] at hh
  exact hh

#print axioms vertex_evaluate

#print axioms representative
#print axioms representative_le
#print axioms representative_fixed
#print axioms representative_merge
#print axioms representative_available
#print axioms representative_evaluate
#print axioms Vertices
#print axioms Representatives
#print axioms verticesFintype
#print axioms representativesFintype
#print axioms compress
#print axioms includeRepresentative
#print axioms compress_include
#print axioms leftVertex
#print axioms rightVertex
#print axioms compress_neighbors
end Verification.PathClassRepresentatives
