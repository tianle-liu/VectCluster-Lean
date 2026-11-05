/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathLiteralEntries
import Verification.PathRhoGrading

/-!
# Path Scalar Naturality

Actual path matrices commute with every change of commutative scalar
ring.  The proof uses the literal word-column recursion and endpoint
projection, independently of any homology or contraction.
-/

namespace Verification.PathScalarNaturality

open Classical Verification.PathRhoFaces Verification.PathRhoWords Verification.PathRhoEndpoint
  Verification.PathEndpointWords Verification.PathEndpointCoordinates
  Verification.PathEndpointComplex Verification.PathLiteralEntries Verification.PathRhoConfiguration

variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)

noncomputable def words : (List Bool →₀ R) →+ (List Bool →₀ S) :=
  Finsupp.mapRange.addMonoidHom φ.toAddMonoidHom

theorem words_apply (f : List Bool →₀ R) (w : List Bool) : words φ f w=φ (f w) := rfl

theorem words_single (w : List Bool) (r : R) :
    words φ (Finsupp.single w r)=Finsupp.single w (φ r) := by
  change Finsupp.mapRange φ (map_zero φ) (Finsupp.single w r)=_
  exact Finsupp.mapRange_single

theorem words_smul (r : R) (f : List Bool →₀ R) : words φ (r • f)=φ r • words φ f := by
  ext w
  exact map_mul φ r (f w)

theorem words_prepend (a : Bool) (f : List Bool →₀ R) :
    words φ (prepend a f)=prepend a (words φ f) := by
  exact (Finsupp.mapDomain_mapRange (List.cons a) f φ (map_zero φ) (map_add φ)).symm

theorem phase_map (ε : R) (a : Bool) : φ (phase ε a)=phase (φ ε) a := by
  cases a <;> simp [phase]

theorem repeat_map (r : R) (a b : Bool) : φ (repeatFactor r a b)=repeatFactor (φ r) a b := by
  cases a <;> cases b <;> simp [repeatFactor]

theorem face_column (ε r : R) (i : ℕ) (w : List Bool) :
    words φ (faceColumn ε r i w)=faceColumn (φ ε) (φ r) i w := by
  induction i generalizing w with
  | zero =>
    cases w with
    | nil => simp [faceColumn]
    | cons a w =>
      cases w with
      | nil => simp [faceColumn]
      | cons b w =>
        cases w with
        | nil => simp [faceColumn]
        | cons c tail =>
          cases b <;> simp only [faceColumn,Bool.false_eq_true,↓reduceIte,map_zero,
            words_smul,words_single,map_one,map_mul,phase_map,repeat_map]
  | succ i ih =>
    cases w with
    | nil => simp [faceColumn]
    | cons a tail => rw [faceColumn,words_smul,words_prepend,ih,phase_map,faceColumn]

theorem evaluation_map (k : R) (a : Bool) : φ (evaluation k a)=evaluation (φ k) a := by
  cases a <;> simp [evaluation]

theorem left_scalar (k : R) (w : List Bool) : φ (leftScalar k w)=leftScalar (φ k) w := by
  cases w
  · exact map_one φ
  · exact evaluation_map φ _ _

theorem right_scalar (k : R) (w : List Bool) : φ (rightScalar k w)=rightScalar (φ k) w := by
  induction w with
  | nil => exact map_one φ
  | cons a w ih =>
    cases w
    · exact evaluation_map φ _ _
    · exact ih

theorem linear_natural
    (P : (List Bool →₀ R) →ₗ[R] (List Bool →₀ R))
    (Q : (List Bool →₀ S) →ₗ[S] (List Bool →₀ S))
    (h : ∀ w,words φ (P (Finsupp.single w 1))=Q (Finsupp.single w 1)) (f : List Bool →₀ R) :
    words φ (P f)=Q (words φ f) := by
  induction f using Finsupp.induction with
  | zero => rw [map_zero,map_zero,map_zero]
  | @single_add w r f _ _ ih =>
    rw [map_add,map_add,map_add,map_add,ih]
    congr 1
    rw [show Finsupp.single w r=r • Finsupp.single w (1:R) by simp,
      map_smul,words_smul,h,words_smul,words_single,map_one,map_smul]

theorem right_projection (k : R) (f : List Bool →₀ R) :
    words φ (Verification.PathRightEndpoint.projection k f)=
      Verification.PathRightEndpoint.projection (φ k) (words φ f) := by
  apply linear_natural
  intro w
  rw [right_projection_column,words_smul,words_single,map_one,right_scalar,right_projection_column]

theorem left_projection (k : R) (f : List Bool →₀ R) :
    words φ (Verification.PathLeftEndpoint.projection k f)=
      Verification.PathLeftEndpoint.projection (φ k) (words φ f) := by
  apply linear_natural
  intro w
  rw [left_projection_column,words_smul,words_single,map_one,left_scalar,left_projection_column]

theorem endpoint (r : R) (n : ℕ) : φ (endpointConstant r n)=endpointConstant (φ r) n := by
  unfold endpointConstant
  split <;> simp

theorem projected_face (g r : R) (n i : ℕ) (w : List Bool) :
    words φ (projectedFace g r n i w)=projectedFace (φ g) (φ r) n i w := by
  rw [projectedFace,right_projection,endpoint,face_column,map_neg]
  rfl

theorem z_matrix (g r : R) (n : ℕ) : (zMatrix g r n).map φ=zMatrix (φ g) (φ r) n := by
  ext y x
  change φ (zMatrix g r n y x)=_
  rw [z_entry,z_entry,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  split
  · rw [map_mul]
    congr 1
    · exact map_pow φ g _
    · exact congrArg (fun f => f y.2.val) (projected_face φ g r n _ x.2.val)
  · exact map_zero φ

theorem y_matrix (g r : R) (a : ℕ) : (yMatrix g r a).map φ=yMatrix (φ g) (φ r) a := by
  ext y x
  change φ (yMatrix g r a y x)=_
  rw [y_entry,y_entry,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  split
  · rw [map_mul]
    congr 1
    · exact map_pow φ g _
    · have hh := left_projection φ 0 (projectedFace g r (2*a) (Verification.PathCompression.faceIndex (Verification.PathCochains.eraseConfig y.1 j).val j) x.2.val)
      rw [map_zero,projected_face] at hh
      exact congrArg (fun f => f y.2.val) hh
  · exact map_zero φ

#print axioms words
#print axioms words_apply
#print axioms words_single
#print axioms words_smul
#print axioms words_prepend
#print axioms phase_map
#print axioms repeat_map
#print axioms face_column
#print axioms evaluation_map
#print axioms left_scalar
#print axioms right_scalar
#print axioms linear_natural
#print axioms right_projection
#print axioms left_projection
#print axioms endpoint
#print axioms projected_face
#print axioms z_matrix
#print axioms y_matrix

end Verification.PathScalarNaturality
