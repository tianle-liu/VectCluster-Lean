/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathRhoWords

/-!
# Path Rho Braid

All-position two-face identities for the actual rho path operator on words.
The mutable faces are separated by at least one nonzero coordinate; deleting
the left normal and merging neighbors shifts the right face index by two.
-/

namespace Verification.PathRhoBraid

open Classical Verification.PathRhoFaces Verification.PathRhoSeparated Verification.PathRhoWords

variable {R : Type*} [CommRing R] (ε ρ : R)

theorem adjacent_word (hε : ε*ε=1) (hρ : ε*ρ=ρ)
    (a i b j c : Bool) (tail : List Bool) :
    face ε ρ 0 (face ε ρ 0 (Finsupp.single (a::i::b::j::c::tail) 1))=
      ε • face ε ρ 0 (face ε ρ 2 (Finsupp.single (a::i::b::j::c::tail) 1)) := by
  have hρε : ρ*ε=ρ := by simpa only [mul_comm] using hρ
  have hρρ : ε*(ρ*ρ)=ρ*ρ := by rw [← mul_assoc,hρ]
  cases a <;> cases i <;> cases b <;> cases j <;> cases c <;>
    simp only [face,Finsupp.linearCombination_single,one_smul,faceColumn,
      phase,repeatFactor,Bool.false_eq_true,Bool.and_false,Bool.and_true,Bool.false_and,
      Bool.true_and,Bool.or_false,Bool.or_true,Bool.false_or,Bool.true_or,↓reduceIte,
      map_zero,map_smul,prepend_single,smul_zero,Finsupp.linearCombination_single,
      one_smul,one_mul,mul_one,smul_smul,hε,hρ,hρε,hρρ]

/-- Unchanged initial symbols contribute twice and therefore cancel exactly. -/
theorem double_face_prepend (hε : ε*ε=1) (i j : ℕ) (a : Bool) (x : List Bool →₀ R) :
    face ε ρ (j+1) (face ε ρ (i+1) (prepend a x))=
      prepend a (face ε ρ j (face ε ρ i x)) := by
  rw [face_prepend,map_smul,face_prepend,smul_smul,phase_squared ε hε,one_smul]

theorem exists_prefix_three (w : List Bool) (h : 3 ≤ w.length) :
    ∃ a b c tail, w=a::b::c::tail := by
  obtain ⟨a,w,rfl⟩ := List.exists_cons_of_length_pos (by omega : 0<w.length)
  simp only [List.length_cons] at h
  obtain ⟨b,w,rfl⟩ := List.exists_cons_of_length_pos (by omega : 0<w.length)
  simp only [List.length_cons] at h
  obtain ⟨c,w,rfl⟩ := List.exists_cons_of_length_pos (by omega : 0<w.length)
  exact ⟨a,b,c,w,rfl⟩

theorem exists_prefix_five (w : List Bool) (h : 5 ≤ w.length) :
    ∃ a b c d e tail, w=a::b::c::d::e::tail := by
  obtain ⟨a,b,c,w,rfl⟩ := exists_prefix_three w (by omega)
  simp only [List.length_cons] at h
  obtain ⟨d,w,rfl⟩ := List.exists_cons_of_length_pos (by omega : 0<w.length)
  simp only [List.length_cons] at h
  obtain ⟨e,w,rfl⟩ := List.exists_cons_of_length_pos (by omega : 0<w.length)
  exact ⟨a,b,c,d,e,w,rfl⟩

/-- Every admissible pair of positions obeys the actual braid; no square identity is assumed. -/
theorem face_braid (hε : ε*ε=1) (hρ : ε*ρ=ρ) (i j : ℕ) (w : List Bool)
    (hij : i+2 ≤ j) (hvalid : j+3 ≤ w.length) :
    face ε ρ (j-2) (face ε ρ i (Finsupp.single w 1))=
      ε • face ε ρ i (face ε ρ j (Finsupp.single w 1)) := by
  induction i generalizing j w with
  | zero =>
    by_cases hj : j=2
    · subst j
      obtain ⟨a,b,c,d,e,tail,rfl⟩ := exists_prefix_five w hvalid
      exact adjacent_word ε ρ hε hρ a b c d e tail
    · have hj₃ : 3 ≤ j := by omega
      obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hj₃
      obtain ⟨a,b,c,tail,rfl⟩ := exists_prefix_three w (by omega)
      have he : Finsupp.single (a::b::c::tail) (1 : R)=
          prepend a (prepend b (prepend c (Finsupp.single tail 1))) := by
        simp only [prepend_single]
      rw [he,show 3+k-2=k+1 by omega,show 3+k=k+3 by omega]
      exact head_tail_diamond ε ρ hε hρ k a b c _
  | succ i ih =>
    cases j with
    | zero => omega
    | succ j =>
      obtain ⟨a,w,rfl⟩ := List.exists_cons_of_length_pos (by omega : 0<w.length)
      simp only [List.length_cons] at hvalid
      have hh := ih j w (by omega) (by omega)
      have hj : j+1-2=(j-2)+1 := by omega
      simp only [Nat.succ_eq_add_one,hj,← prepend_single]
      rw [double_face_prepend ε ρ hε,double_face_prepend ε ρ hε,hh,map_smul]

/-- At arbitrary valid positions the original g incidence factors cancel the full rho maps. -/
theorem face_pair_cancellation (g : R) (hg : g*g=1) (hr : (1+g)*ρ=0)
    (i j : ℕ) (w : List Bool) (hij : i+2 ≤ j) (hvalid : j+3 ≤ w.length) :
    g • face (-g) ρ (j-2) (face (-g) ρ i (Finsupp.single w 1))+
      face (-g) ρ i (face (-g) ρ j (Finsupp.single w 1))=0 := by
  obtain ⟨hε,hρ⟩ := epsilon_relations ρ g hg hr
  rw [face_braid (-g) ρ hε hρ i j w hij hvalid,smul_smul]
  have hh : g*(-g)= -1 := by rw [mul_neg,hg]
  rw [hh,neg_one_smul,neg_add_cancel]

#print axioms adjacent_word
#print axioms double_face_prepend
#print axioms exists_prefix_three
#print axioms exists_prefix_five
#print axioms face_braid
#print axioms face_pair_cancellation

end Verification.PathRhoBraid
