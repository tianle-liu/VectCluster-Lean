/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathRhoSeparated
import Mathlib.LinearAlgebra.Finsupp.LSum
import Lean.Elab.Tactic.Omega

/-!
# Path Rho Words

The rho-corrected local face on arbitrary binary words, preserving unchanged
prefixes and suffixes literally. This will supply finite length restrictions
for the complete stratum-indexed path model.
-/

namespace Verification.PathRhoWords

open Classical Verification.PathRhoFaces Verification.PathRhoSeparated

variable {R : Type*} [CommRing R] (ε ρ : R)

noncomputable def prepend (a : Bool) : (List Bool →₀ R) →ₗ[R] (List Bool →₀ R) :=
  Finsupp.lmapDomain R R (List.cons a)

theorem prepend_single (a : Bool) (w : List Bool) (r : R) :
    prepend (R := R) a (Finsupp.single w r)=Finsupp.single (a::w) r := by
  simp only [prepend,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]

/-- Position i specifies the left neighbor of the contracted normal vertex. -/
noncomputable def faceColumn : ℕ → List Bool → (List Bool →₀ R)
  | 0, a::b::c::tail =>
      if b then (phase ε a*repeatFactor ρ a c) • Finsupp.single ((a || c)::tail) 1 else 0
  | 0, _ => 0
  | i+1, a::tail => phase ε a • prepend a (faceColumn i tail)
  | _+1, [] => 0

noncomputable def face (i : ℕ) : (List Bool →₀ R) →ₗ[R] (List Bool →₀ R) :=
  Finsupp.linearCombination R (faceColumn ε ρ i)

theorem face_single (i : ℕ) (w : List Bool) :
    face ε ρ i (Finsupp.single w 1)=faceColumn ε ρ i w := by
  simp only [face,Finsupp.linearCombination_single,one_smul]

theorem face_nil (i : ℕ) : face ε ρ i (Finsupp.single [] 1)=0 := by
  rw [face_single]
  cases i <;> rfl

/-- The complete preceding-coordinate factor, including arbitrary linear combinations. -/
theorem face_prepend (i : ℕ) (a : Bool) (x : List Bool →₀ R) :
    face ε ρ (i+1) (prepend a x)=phase ε a • prepend a (face ε ρ i x) := by
  have hh : (face ε ρ (i+1)).comp (prepend a)=
      phase ε a • (prepend a).comp (face ε ρ i) := by
    apply Finsupp.lhom_ext
    intro w r
    have hr : Finsupp.single w r=r • Finsupp.single w (1 : R) := by simp
    rw [hr,map_smul,map_smul]
    congr 1
    simp only [LinearMap.comp_apply,prepend_single,face_single,faceColumn,
      LinearMap.smul_apply]
  exact congrArg (fun f : _ →ₗ[R] _ => f x) hh

/-- Head contraction with its rho term is valid for every remaining suffix module element. -/
theorem face_head (a b c : Bool) (x : List Bool →₀ R) :
    face ε ρ 0 (prepend a (prepend b (prepend c x)))=
      if b then (phase ε a*repeatFactor ρ a c) • prepend (a || c) x else 0 := by
  have hh : (face ε ρ 0).comp ((prepend a).comp ((prepend b).comp (prepend c)))=
      if b then (phase ε a*repeatFactor ρ a c) • prepend (a || c) else 0 := by
    apply Finsupp.lhom_ext
    intro w r
    have hr : Finsupp.single w r=r • Finsupp.single w (1 : R) := by simp
    rw [hr,map_smul,map_smul]
    congr 1
    cases b <;> simp only [LinearMap.comp_apply,prepend_single,face_single,faceColumn,
      Bool.false_eq_true,↓reduceIte,LinearMap.smul_apply,LinearMap.zero_apply]
  have he := congrArg (fun f : _ →ₗ[R] _ => f x) hh
  cases b <;> simpa only [LinearMap.comp_apply,Bool.false_eq_true,↓reduceIte,
    LinearMap.smul_apply,LinearMap.zero_apply] using he

theorem face_short (i : ℕ) (w : List Bool) (h : w.length<i+3) : faceColumn ε ρ i w=0 := by
  induction i generalizing w with
  | zero =>
    cases w with
    | nil => rfl
    | cons a w =>
      cases w with
      | nil => rfl
      | cons b w =>
        cases w with
        | nil => rfl
        | cons c w => simp only [List.length_cons] at h; omega
  | succ i ih =>
    cases w with
    | nil => rfl
    | cons a w =>
      rw [faceColumn, ih w (by simp only [List.length_cons] at h; omega),map_zero,smul_zero]

/-- Removing disjoint triples obeys the braided face relation for an arbitrary suffix. -/
theorem head_tail_diamond (hε : ε*ε=1) (hρ : ε*ρ=ρ)
    (k : ℕ) (a b c : Bool) (x : List Bool →₀ R) :
    face ε ρ (k+1) (face ε ρ 0 (prepend a (prepend b (prepend c x))))=
      ε • face ε ρ 0 (face ε ρ (k+3) (prepend a (prepend b (prepend c x)))) := by
  have hskip : face ε ρ (k+3) (prepend a (prepend b (prepend c x)))=
      (phase ε a*phase ε b*phase ε c) • prepend a (prepend b (prepend c (face ε ρ k x))) := by
    rw [show k+3=(k+2)+1 by omega,face_prepend,
      show k+2=(k+1)+1 by omega,face_prepend,face_prepend,map_smul,map_smul]
    simp only [map_smul,smul_smul,mul_assoc]
  rw [face_head,hskip,map_smul,face_head]
  cases b with
  | false => simp only [Bool.false_eq_true,↓reduceIte,map_zero,smul_zero]
  | true =>
    simp only [↓reduceIte,map_smul,face_prepend,smul_smul]
    congr 1
    change (phase ε a*repeatFactor ρ a c)*phase ε (a || c)=
      ε*((phase ε a*ε*phase ε c)*(phase ε a*repeatFactor ρ a c))
    calc
      _=phase ε a*phase ε (a || c)*repeatFactor ρ a c := by ring
      _=phase ε c*repeatFactor ρ a c := phase_merge ε ρ hε hρ a c
      _=(ε*ε)*(phase ε a*phase ε a)*(phase ε c*repeatFactor ρ a c) := by
        rw [hε,phase_squared ε hε,one_mul,one_mul]
      _=_ := by ring

#print axioms prepend
#print axioms prepend_single
#print axioms faceColumn
#print axioms face
#print axioms face_single
#print axioms face_nil
#print axioms face_prepend
#print axioms face_head
#print axioms face_short
#print axioms head_tail_diamond

end Verification.PathRhoWords
