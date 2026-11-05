/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathRhoWords
import Mathlib.Data.List.Count

/-!
# Path Rho Grading

Exact degree accounting for every actual path face column. It is zero or
a single monomial coefficient epsilon^k rho^d; the rho exponent is proved equal
to the weight drop, and is at most one for each face.
-/

namespace Verification.PathRhoGrading

open Classical Verification.PathRhoFaces Verification.PathRhoWords

variable {R : Type*} [CommRing R] (ε ρ : R)

/-- An actual column has a single target word, with its precise formal weight degree. -/
theorem column_monomial (i : ℕ) (w : List Bool) :
    faceColumn ε ρ i w=0 ∨ ∃ (k d : ℕ) (v : List Bool),
      d ≤ 1 ∧ v.length+2=w.length ∧ v.count true+1+d=w.count true ∧
      faceColumn ε ρ i w=(ε^k*ρ^d) • Finsupp.single v 1 := by
  induction i generalizing w with
  | zero =>
    cases w with
    | nil => exact Or.inl rfl
    | cons a w =>
      cases w with
      | nil => exact Or.inl rfl
      | cons b w =>
        cases w with
        | nil => exact Or.inl rfl
        | cons c tail =>
          cases b with
          | false => exact Or.inl rfl
          | true =>
            cases a <;> cases c
            · exact Or.inr ⟨0,0,false::tail,by omega,by simp,by simp,
                by simp [faceColumn,phase,repeatFactor]⟩
            · exact Or.inr ⟨0,0,true::tail,by omega,by simp,by simp,
                by simp [faceColumn,phase,repeatFactor]⟩
            · exact Or.inr ⟨1,0,true::tail,by omega,by simp,by simp,
                by simp [faceColumn,phase,repeatFactor]⟩
            · exact Or.inr ⟨1,1,true::tail,by omega,by simp,by simp,
                by simp [faceColumn,phase,repeatFactor]⟩
  | succ i ih =>
    cases w with
    | nil => exact Or.inl rfl
    | cons a w =>
      rcases ih w with hz | ⟨k,d,v,hd,hlen,hcount,hform⟩
      · exact Or.inl (by rw [faceColumn,hz,map_zero,smul_zero])
      · cases a with
        | false =>
          refine Or.inr ⟨k,d,false::v,hd,?_,?_,?_⟩
          · simp only [List.length_cons]; omega
          · simpa using hcount
          · simp only [faceColumn,hform,map_smul,prepend_single,phase,Bool.false_eq_true,
              ↓reduceIte,one_smul]
        | true =>
          refine Or.inr ⟨k+1,d,true::v,hd,?_,?_,?_⟩
          · simp only [List.length_cons]; omega
          · simp only [List.count_cons_self]; omega
          · simp only [faceColumn,hform,map_smul,prepend_single,phase,↓reduceIte,smul_smul]
            congr 1
            rw [pow_succ]
            ring

/-- Thus every nonzero coefficient goes from a longer word to exactly two fewer coordinates. -/
theorem column_length (i : ℕ) (w : List Bool) :
    faceColumn ε ρ i w=0 ∨ ∃ (c : R) (v : List Bool), v.length+2=w.length ∧
      faceColumn ε ρ i w=c • Finsupp.single v 1 := by
  rcases column_monomial ε ρ i w with hz | ⟨k,d,v,_,hl,_,hf⟩
  · exact Or.inl hz
  · exact Or.inr ⟨ε^k*ρ^d,v,hl,hf⟩

/-- Including stratum degree, rho-degree exactly compensates the cochain weight decrease. -/
theorem column_weight (i : ℕ) (w : List Bool) (p : ℕ) :
    faceColumn ε ρ i w=0 ∨ ∃ (k d : ℕ) (v : List Bool),
      d ≤ 1 ∧ (p+1)+v.count true+d=p+w.count true ∧
      faceColumn ε ρ i w=(ε^k*ρ^d) • Finsupp.single v 1 := by
  rcases column_monomial ε ρ i w with hz | ⟨k,d,v,hd,_,hc,hf⟩
  · exact Or.inl hz
  · exact Or.inr ⟨k,d,v,hd,by omega,hf⟩

#print axioms column_monomial
#print axioms column_length
#print axioms column_weight

end Verification.PathRhoGrading
