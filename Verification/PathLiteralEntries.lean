/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathNormalBasisCoefficients
import Verification.PathCoefficientInclusion

/-!
# Path Literal Entries

Literal entries of every full-rho path face matrix, in all homological
degrees.  This removes the basis-equivalence wrappers before scalar and
coefficient-degree calculations.
-/

namespace Verification.PathLiteralEntries

open Classical Verification.PathCompression Verification.PathCochains Verification.PathRhoWords
  Verification.PathRhoConfiguration Verification.PathEndpointComplex
  Verification.PathEndpointWords Verification.PathNormalizedBasis Verification.PathEndpointCoordinates
  Verification.PathNormalBasisCoefficients Verification.PathStratumGrading

variable {R : Type*} [CommRing R]

theorem z_inverse (ρ : R) (n : ℕ) (x : NormalIndex RightNormal n) (I : Config n) :
    (((zCoefficients ρ n).symm (Pi.single x 1)).val I).val=
      if I=x.1 then Finsupp.single x.2.val 1 else 0 := by
  by_cases he : I=x.1
  · subst I
    rw [if_pos rfl]
    exact zCoefficients_inverse_word ρ n x.1 x.2
  · rw [if_neg he,zCoefficients_inverse_stratum ρ n x I he]
    rfl

theorem y_inverse (ρ : R) (a : ℕ) (x : NormalIndex BothNormal (2*a)) (I : Config (2*a)) :
    (((yCoefficients ρ a).symm (Pi.single x 1)).val I).val=
      if I=x.1 then Finsupp.single x.2.val 1 else 0 := by
  by_cases he : I=x.1
  · subst I
    rw [if_pos rfl]
    exact yCoefficients_inverse_word ρ a x.1 x.2
  · rw [if_neg he,yCoefficients_inverse_stratum ρ a x I he]
    rfl

noncomputable def projectedFace (g ρ : R) (n i : ℕ) (w : List Bool) : List Bool →₀ R :=
  Verification.PathRightEndpoint.projection (endpointConstant ρ n) (faceColumn (-g) ρ i w)

theorem z_entry (g ρ : R) (n : ℕ) (y x : NormalIndex RightNormal n) :
    zMatrix g ρ n y x=∑ j∈y.1.val,
      if eraseConfig y.1 j=x.1 then incidence g (eraseConfig y.1 j).val j *
        projectedFace g ρ n (faceIndex (eraseConfig y.1 j).val j) x.2.val y.2.val else 0 := by
  simp only [zMatrix,matrixOf,LinearMap.toMatrix'_apply,LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [show (fun i : NormalIndex RightNormal n => if i=x then (1 : R) else 0)=
    Pi.single x 1 by funext i; simp [Pi.single_apply,eq_comm]]
  rw [zCoefficients_apply]
  change Verification.PathRightEndpoint.projection (endpointConstant ρ n)
    (ambientDifferential g ρ n (inclusion n ((zCoefficients ρ n).symm (Pi.single x 1)).val) y.1)
      y.2.val=_
  rw [ambientDifferential_apply,map_sum,Finsupp.finset_sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  change Verification.PathRightEndpoint.projection (endpointConstant ρ n)
    (faceMap g ρ (eraseConfig y.1 j).val j
      (((zCoefficients ρ n).symm (Pi.single x 1)).val (eraseConfig y.1 j)).val) y.2.val=_
  rw [z_inverse]
  by_cases he : eraseConfig y.1 j=x.1
  · rw [if_pos he,if_pos he]
    simp only [faceMap,LinearMap.smul_apply,face_single,map_smul,Finsupp.smul_apply,smul_eq_mul]
    rfl
  · rw [if_neg he,if_neg he,map_zero,map_zero,Finsupp.zero_apply]

theorem y_entry (g ρ : R) (a : ℕ) (y x : NormalIndex BothNormal (2*a)) :
    yMatrix g ρ a y x=∑ j∈y.1.val,
      if eraseConfig y.1 j=x.1 then incidence g (eraseConfig y.1 j).val j *
        (Verification.PathLeftEndpoint.projection 0
          (projectedFace g ρ (2*a) (faceIndex (eraseConfig y.1 j).val j) x.2.val)) y.2.val else 0 := by
  simp only [yMatrix,matrixOf,LinearMap.toMatrix'_apply,LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [show (fun i : NormalIndex BothNormal (2*a) => if i=x then (1 : R) else 0)=
    Pi.single x 1 by funext i; simp [Pi.single_apply,eq_comm]]
  rw [yCoefficients_apply]
  change Verification.PathLeftEndpoint.projection 0
    (Verification.PathRightEndpoint.projection (endpointConstant ρ (2*a))
    (ambientDifferential g ρ (2*a) (inclusion (2*a) ((yCoefficients ρ a).symm (Pi.single x 1)).val) y.1))
      y.2.val=_
  rw [ambientDifferential_apply,map_sum,map_sum,Finsupp.finset_sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  change Verification.PathLeftEndpoint.projection 0
    (Verification.PathRightEndpoint.projection (endpointConstant ρ (2*a))
    (faceMap g ρ (eraseConfig y.1 j).val j
      (((yCoefficients ρ a).symm (Pi.single x 1)).val (eraseConfig y.1 j)).val)) y.2.val=_
  rw [y_inverse]
  by_cases he : eraseConfig y.1 j=x.1
  · rw [if_pos he,if_pos he]
    simp only [faceMap,LinearMap.smul_apply,face_single,map_smul,Finsupp.smul_apply,smul_eq_mul]
    rfl
  · rw [if_neg he,if_neg he,map_zero,map_zero,map_zero,Finsupp.zero_apply]

#print axioms z_inverse
#print axioms y_inverse
#print axioms projectedFace
#print axioms z_entry
#print axioms y_entry

end Verification.PathLiteralEntries
