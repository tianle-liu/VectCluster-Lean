/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SignComplex
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-!
# Subset Projection Complex

The alternating subset differential for commuting coefficient projections.
This proof is independent of signature functions and uses only genuine
linear endomorphisms of one ambient coefficient module.
-/
noncomputable section
namespace Verification.SubsetProjectionComplex
variable {V A : Type*} [Fintype V] [LinearOrder V] [AddCommGroup A]

def sign (J : Finset V) (i : V) : ℤ := (-1)^((J.filter (fun j => j<i)).card)

theorem signs_opposite (J : Finset V) (i j : V) (hi : i∈J) (hj : j∈J) (hij : i≠j) :
    sign J i * sign (J.erase i) j = -(sign J j * sign (J.erase j) i) := by
  let s : Verification.SignComplex.State V := fun v => if v∈J then none else some false
  have hs : Verification.SignComplex.holes s = J := by
    ext v
    simp [Verification.SignComplex.holes,s]
  have h := Verification.SignComplex.incidence_sign_opposite s i j
    (by simp [s,hi]) (by simp [s,hj]) hij false false
  simpa only [Verification.SignComplex.incidenceSign,Verification.SignComplex.incidenceRank,
    Verification.SignComplex.holes_faceState,hs,sign] using h

variable (P : V → A →+ A)

def face (i : V) (f : Finset V → A) (J : Finset V) : A :=
  if i∈J then sign J i • P i (f (J.erase i)) else 0

def differential (f : Finset V → A) : Finset V → A := fun J => ∑ i, face P i f J

omit [Fintype V] in
theorem face_add (i : V) (f g : Finset V → A) (J : Finset V) :
    face P i (f+g) J = face P i f J + face P i g J := by
  by_cases hi : i∈J <;> simp [face,hi,map_add,smul_add]

omit [Fintype V] in
theorem face_zero (i : V) (J : Finset V) : face P i (0 : Finset V → A) J = 0 := by
  simp [face]

omit [Fintype V] in
theorem face_sum {ι : Type*} (s : Finset ι) (f : ι → Finset V → A) (i : V) (J : Finset V) :
    face P i (fun I => ∑ a∈s, f a I) J = ∑ a∈s, face P i (f a) J := by
  by_cases hi : i∈J <;> simp [face,hi,map_sum,Finset.smul_sum]

omit [Fintype V] in
theorem face_same (i : V) (f : Finset V → A) (J : Finset V) :
    face P i (face P i f) J = 0 := by
  simp [face]

omit [Fintype V] in
theorem face_twice (i j : V) (f : Finset V → A) (J : Finset V)
    (hi : i∈J) (hj : j∈J) (hij : i≠j) :
    face P i (face P j f) J =
      (sign J i * sign (J.erase i) j) • P i (P j (f ((J.erase i).erase j))) := by
  simp [face,hi,hj,hij,hij.symm,map_zsmul,mul_smul]

include P in
theorem faces_anticommute (hP : ∀ i j a, P i (P j a) = P j (P i a))
    (i j : V) (f : Finset V → A) (J : Finset V) (hij : i≠j) :
    face P i (face P j f) J + face P j (face P i f) J = 0 := by
  by_cases hi : i∈J
  · by_cases hj : j∈J
    · rw [face_twice P i j f J hi hj hij,face_twice P j i f J hj hi hij.symm,
        signs_opposite J i j hi hj hij,Finset.erase_right_comm,hP i j]
      simp
    · simp [face,hi,hj,Finset.mem_erase]
  · simp [face,hi,Finset.mem_erase]

theorem differential_squared (hP : ∀ i j a, P i (P j a) = P j (P i a))
    (f : Finset V → A) (J : Finset V) : differential P (differential P f) J = 0 := by
  unfold differential
  simp_rw [face_sum]
  rw [← Finset.sum_product']
  apply Finset.sum_involution (fun p _ => (p.2,p.1))
  · intro p _
    by_cases h : p.1 = p.2
    · simp [h,face_same]
    · exact faces_anticommute P hP p.1 p.2 f J h
  · intro p _ hn he
    have h : p.1 = p.2 := congrArg Prod.snd he
    exact hn (by simpa [h] using face_same P p.2 f J)
  · intro p _
    simp only [Finset.mem_product,Finset.mem_univ,and_self]
  · intro p _
    cases p
    rfl

theorem differential_formula (f : Finset V → A) (J : Finset V) :
    differential P f J = ∑ i∈J, sign J i • P i (f (J.erase i)) := by
  classical
  simp only [differential,face,← Finset.sum_filter]
  simp

#print axioms sign
#print axioms signs_opposite
#print axioms face
#print axioms differential
#print axioms face_add
#print axioms face_zero
#print axioms face_sum
#print axioms face_same
#print axioms face_twice
#print axioms faces_anticommute
#print axioms differential_squared
#print axioms differential_formula
end Verification.SubsetProjectionComplex
