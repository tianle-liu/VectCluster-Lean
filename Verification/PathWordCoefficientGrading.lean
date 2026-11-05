/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathCoefficientGrading
import Verification.PathEndpointWords

/-!
# Path Word Coefficient Grading

The actual rho face columns and constant-endpoint evaluations have the
coefficient degree forced by the loss of selected binary coordinates.
-/

namespace Verification.PathWordCoefficientGrading

open Verification.PathCoefficientRing Verification.PathCoefficientGrading
  Verification.PathRhoFaces Verification.PathRhoWords Verification.PathRhoEndpoint
  Verification.PathEndpointWords

variable (ε r k : Coeff)

theorem count_cons (a : Bool) (w : List Bool) :
    ((a::w).count true:ℤ)=(if a then 1 else 0)+(w.count true:ℤ) := by
  cases a <;> simp [add_comm]

theorem phase_homogeneous (hε : Homogeneous 0 ε) (a : Bool) : Homogeneous 0 (phase ε a) := by
  cases a
  · exact homogeneous_one
  · exact hε

theorem merge_homogeneous (hε : Homogeneous 0 ε) (hr : Homogeneous 1 r)
    (a c : Bool) (tail : List Bool) :
    Homogeneous (((a::true::c::tail).count true:ℤ)-((a || c)::tail).count true-1)
      (phase ε a*repeatFactor r a c) := by
  cases a <;> cases c
  · simpa [phase,repeatFactor,count_cons] using (homogeneous_mul homogeneous_one homogeneous_one)
  · simpa [phase,repeatFactor,count_cons] using (homogeneous_mul homogeneous_one homogeneous_one)
  · simpa [phase,repeatFactor,count_cons] using (homogeneous_mul hε homogeneous_one)
  · have he : (((true::true::true::tail).count true:ℤ)-((true || true)::tail).count true-1)=1 := by
      simp [count_cons]
      omega
    rw [he]
    exact homogeneous_mul hε hr

theorem face_column (hε : Homogeneous 0 ε) (hr : Homogeneous 1 r)
    (i : ℕ) (w : List Bool) :
    ∃ c : Coeff,∃ v : List Bool,faceColumn ε r i w=c • Finsupp.single v 1 ∧
      Homogeneous ((w.count true:ℤ)-v.count true-1) c := by
  induction i generalizing w with
  | zero =>
    cases w with
    | nil => exact ⟨0,[],by simp [faceColumn],homogeneous_zero _⟩
    | cons a w =>
      cases w with
      | nil => exact ⟨0,[],by simp [faceColumn],homogeneous_zero _⟩
      | cons b w =>
        cases w with
        | nil => exact ⟨0,[],by simp [faceColumn],homogeneous_zero _⟩
        | cons c tail =>
          cases b with
          | false => exact ⟨0,[],by simp [faceColumn],homogeneous_zero _⟩
          | true => exact ⟨phase ε a*repeatFactor r a c,(a || c)::tail,rfl,
              merge_homogeneous ε r hε hr a c tail⟩
  | succ i ih =>
    cases w with
    | nil => exact ⟨0,[],by simp [faceColumn],homogeneous_zero _⟩
    | cons a tail =>
      obtain ⟨c,v,hc,hg⟩ := ih tail
      refine ⟨phase ε a*c,a::v,?_,?_⟩
      · rw [faceColumn,hc,map_smul,prepend_single,smul_smul]
      · have h := homogeneous_mul (phase_homogeneous ε hε a) hg
        convert h using 1
        simp only [count_cons]
        omega

theorem evaluation_homogeneous (hk : Homogeneous 1 k) (a : Bool) :
    Homogeneous (if a then 1 else 0) (evaluation k a) := by
  cases a
  · exact homogeneous_one
  · exact hk

theorem left_scalar (hk : Homogeneous 1 k) (w : List Bool) :
    Homogeneous ((w.count true:ℤ)-(normalizeLeft w).count true) (leftScalar k w) := by
  cases w with
  | nil => simpa [leftScalar,normalizeLeft] using homogeneous_one
  | cons a tail =>
    simpa [leftScalar,normalizeLeft,count_cons] using evaluation_homogeneous k hk a

theorem right_scalar (hk : Homogeneous 1 k) (w : List Bool) :
    Homogeneous ((w.count true:ℤ)-(normalizeRight w).count true) (rightScalar k w) := by
  induction w with
  | nil => simpa [rightScalar,normalizeRight] using homogeneous_one
  | cons a w ih =>
    cases w with
    | nil => simpa [rightScalar,normalizeRight,count_cons] using evaluation_homogeneous k hk a
    | cons b tail =>
      change Homogeneous (((a::b::tail).count true:ℤ)-(a::normalizeRight (b::tail)).count true)
        (rightScalar k (b::tail))
      convert ih using 1
      simp only [count_cons]
      omega

#print axioms count_cons
#print axioms phase_homogeneous
#print axioms merge_homogeneous
#print axioms face_column
#print axioms evaluation_homogeneous
#print axioms left_scalar
#print axioms right_scalar

end Verification.PathWordCoefficientGrading
