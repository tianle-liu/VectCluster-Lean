/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathAffineSigns
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination

/-!
# Path Affine Faces

Full-rho compatibility of actual affine sign substitutions with local
path residue faces. Period-two signs agree on the two neighbor coordinates.
-/

namespace Verification.PathAffineFaces

open Classical Verification.PathRhoWords Verification.PathRhoFaces Verification.PathAffineSigns

variable {R : Type*} [CommRing R] (g ρ : R)

theorem far_prefix (hr : (1+g)*ρ=0) (i : ℕ) (a bit : Bool) (x : List Bool →₀ R) :
    face (-g) ρ (i+1) (prefixMap g ρ a bit x)=
      phase (-g) bit • prefixMap g ρ a bit (face (-g) ρ i x) := by
  have hρ : -g*ρ=ρ := by linear_combination -hr
  cases a <;> cases bit <;>
    simp only [prefixMap,Bool.false_eq_true,↓reduceIte,LinearMap.add_apply,LinearMap.smul_apply,
      map_add,map_smul,face_prepend,phase,Bool.false_eq_true,↓reduceIte,
      smul_add,smul_smul,one_smul]
  rw [hρ]
  module

/-- A flipped normal contributes g; flipped equal neighbors obey the same rho multiplication. -/
theorem head_prefix (hg : g*g=1) (hr : (1+g)*ρ=0)
    (a b l m r : Bool) (x : List Bool →₀ R) :
    face (-g) ρ 0 (prefixMap g ρ a l (prefixMap g ρ b m (prefixMap g ρ a r x)))=
      (if b then g else 1) •
        (if m then (phase (-g) l*repeatFactor ρ l r) • prefixMap g ρ a (l || r) x else 0) := by
  have hg2 : g^2=1 := by simpa only [pow_two] using hg
  have hg3 : g^3=g := by simp only [pow_succ,hg2,one_mul]
  have hg4 : g^4=1 := by simpa only [pow_succ,hg3] using hg
  have hgr : g*ρ= -ρ := by linear_combination hr
  have hrg : ρ*g= -ρ := by rw [mul_comm,hgr]
  have hrg2 : ρ^2*g= -(ρ^2) := by calc
    _=ρ*(ρ*g) := by ring
    _=ρ*(-ρ) := by rw [hrg]
    _=_ := by ring
  cases a <;> cases b <;> cases l <;> cases m <;> cases r <;>
    simp only [prefixMap,Bool.false_eq_true,↓reduceIte,LinearMap.add_apply,LinearMap.smul_apply,
      map_add,map_smul,face_head,phase,repeatFactor,Bool.false_eq_true,↓reduceIte,
      Bool.false_or,Bool.true_or,Bool.false_and,Bool.true_and,smul_add,smul_smul,
      one_smul,map_zero,smul_zero,mul_one,one_mul] <;>
    match_scalars <;> ring_nf <;> simp only [hg2,hg3,hg4,hgr,hrg,hrg2] <;> ring

#print axioms far_prefix
#print axioms head_prefix

end Verification.PathAffineFaces
