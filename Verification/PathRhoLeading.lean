/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathFirstCofaces
import Verification.PathRhoGrading

/-!
# Path Rho Leading

On the original weight-preserving diagonal every full-rho face agrees
literally with its rho-zero specialization. The remaining entries strictly
lower cochain weight, or strictly raise chain weight after transpose.
-/

namespace Verification.PathRhoLeading

open Classical Verification.PathRhoFaces Verification.PathRhoWords Verification.PathFirstCofaces

variable {R : Type*} [CommRing R]

theorem coface_leading (ε ρ : R) (i : ℕ) (v w : List Bool)
    (h : w.count true ≤ v.count true+1) :
    cofaceColumn ε ρ i v w=cofaceColumn ε 0 i v w := by
  induction i generalizing v w with
  | zero =>
    cases v with
    | nil => rfl
    | cons bit tail =>
      cases bit with
      | false => rfl
      | true =>
        have hn : w ≠ true::true::true::tail := by
          intro he
          subst w
          simp only [List.count_cons_self] at h
          omega
        simp only [cofaceColumn,Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul,
          Finsupp.single_apply,Ne.symm hn,↓reduceIte,mul_zero,add_zero]
  | succ i ih =>
    cases v with
    | nil => rfl
    | cons bit tail =>
      simp only [cofaceColumn,Finsupp.smul_apply,smul_eq_mul]
      cases w with
      | nil => rw [prepend_nil,prepend_nil]
      | cons head rest =>
        by_cases hb : bit=head
        · subst head
          rw [prepend_same,prepend_same]
          congr 1
          apply ih
          cases bit <;> simp [List.count_cons] at h ⊢ <;> omega
        · rw [prepend_other bit head hb,prepend_other bit head hb]

/-- This is an equality of coefficients of the actual cochain face maps. -/
theorem face_leading (ε ρ : R) (i : ℕ) (w v : List Bool)
    (h : w.count true ≤ v.count true+1) :
    faceColumn ε ρ i w v=faceColumn ε 0 i w v := by
  rw [coface_adjoint,coface_adjoint]
  exact coface_leading ε ρ i v w h

/-- Including the stratum cardinality, any rho-dependent coefficient is strictly weight-decreasing. -/
theorem face_difference_strict (ε ρ : R) (i p : ℕ) (w v : List Bool)
    (h : p+w.count true ≤ (p+1)+v.count true) :
    (faceColumn ε ρ i w-faceColumn ε 0 i w) v=0 := by
  rw [Finsupp.sub_apply,face_leading ε ρ i w v (by omega),sub_self]

#print axioms coface_leading
#print axioms face_leading
#print axioms face_difference_strict

end Verification.PathRhoLeading
