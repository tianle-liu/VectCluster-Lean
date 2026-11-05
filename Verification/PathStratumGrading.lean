/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathEndpointCoordinates
import Verification.GradedPerturbation

/-!
# Path Stratum Grading

The full-rho finite matrices have the literal cellular degree |I|.
-/

namespace Verification.PathStratumGrading

open Classical Verification.PathCompression Verification.PathCochains
  Verification.PathRhoConfiguration Verification.PathRhoFinite
  Verification.PathEndpointComplex Verification.PathEndpointWords
  Verification.PathNormalizedBasis Verification.PathEndpointBasis Verification.PathEndpointCoordinates

variable {R : Type*} [CommRing R]

theorem normalCoordinates_inverse_stratum (B : List Bool → Prop) (n : ℕ)
    (k : NormalIndex B n) (I : Config n) (hI : I ≠ k.1) :
    (normalCoordinates (R := R) B n).symm (Pi.single k 1) I=0 := by
  apply Subtype.ext
  apply Finsupp.ext
  intro w
  by_cases hw : w.length=(available I.val (n+2)).card ∧ B w
  · have hk : (⟨I,⟨w,hw⟩⟩ : NormalIndex B n) ≠ k := by
      intro he
      exact hI (congrArg Sigma.fst he)
    have he := congrFun ((normalCoordinates (R := R) B n).apply_symm_apply (Pi.single k 1))
      (⟨I,⟨w,hw⟩⟩ : NormalIndex B n)
    rw [normalCoordinates_apply] at he
    simpa only [Pi.single_eq_of_ne hk,Finsupp.zero_apply] using he
  · have hh := ((normalCoordinates (R := R) B n).symm (Pi.single k 1) I).property
    exact (Finsupp.mem_supported' R _).mp hh w hw

theorem zCoefficients_inverse_stratum (ρ : R) (n : ℕ)
    (k : NormalIndex RightNormal n) (I : Config n) (hI : I ≠ k.1) :
    ((zCoefficients ρ n).symm (Pi.single k 1)).val I=0 := by
  apply Subtype.ext
  change ((normalCoordinates (R := R) RightNormal n).symm (Pi.single k 1) I).val=0
  exact congrArg Subtype.val (normalCoordinates_inverse_stratum RightNormal n k I hI)

theorem yCoefficients_inverse_stratum (ρ : R) (a : ℕ)
    (k : NormalIndex BothNormal (2*a)) (I : Config (2*a)) (hI : I ≠ k.1) :
    ((yCoefficients ρ a).symm (Pi.single k 1)).val I=0 := by
  apply Subtype.ext
  change ((normalCoordinates (R := R) BothNormal (2*a)).symm (Pi.single k 1) I).val=0
  exact congrArg Subtype.val (normalCoordinates_inverse_stratum BothNormal (2*a) k I hI)

theorem differential_stratum_zero (g ρ : R) (n : ℕ) (x : Total (R := R) n) (J : Config n)
    (hx : ∀ j ∈ J.val, x (eraseConfig J j)=0) : differential g ρ n x J=0 := by
  apply Subtype.ext
  change ambientDifferential g ρ n (inclusion n x) J=0
  rw [ambientDifferential_apply]
  apply Finset.sum_eq_zero
  intro j hj
  change faceMap g ρ (eraseConfig J j).val j (x (eraseConfig J j)).val=0
  rw [hx j hj]
  exact map_zero _

theorem zDifferential_stratum_zero (g ρ : R) (n : ℕ) (x : ZModule ρ n) (J : Config n)
    (hx : ∀ j ∈ J.val, x.val (eraseConfig J j)=0) : (zDifferential g ρ n x).val J=0 := by
  apply Subtype.ext
  change Verification.PathRightEndpoint.projection (endpointConstant ρ n)
    (differential g ρ n x.val J).val=0
  rw [differential_stratum_zero g ρ n x.val J hx]
  exact map_zero _

theorem yDifferential_stratum_zero (g ρ : R) (a : ℕ) (x : YModule ρ a) (J : Config (2*a))
    (hx : ∀ j ∈ J.val, x.val (eraseConfig J j)=0) : (yDifferential g ρ a x).val J=0 := by
  apply Subtype.ext
  change Verification.PathLeftEndpoint.projection 0
    (Verification.PathRightEndpoint.projection (endpointConstant ρ (2*a))
      (differential g ρ (2*a) x.val J).val)=0
  rw [differential_stratum_zero g ρ (2*a) x.val J hx]
  change Verification.PathLeftEndpoint.projection 0
    (Verification.PathRightEndpoint.projection (endpointConstant ρ (2*a)) 0)=0
  rw [map_zero,map_zero]

/-- The original independent-zero-set cellular degree. -/
def degree {B : List Bool → Prop} {n : ℕ} (x : NormalIndex B n) : ℤ := x.1.val.card

theorem erase_stratum_ne {B : List Bool → Prop} {n : ℕ} (y x : NormalIndex B n)
    (h : degree y ≠ degree x+1) (j : ℕ) (hj : j ∈ y.1.val) : eraseConfig y.1 j ≠ x.1 := by
  intro he
  have hc := Finset.card_erase_add_one hj
  have hv : y.1.val.erase j=x.1.val := congrArg Subtype.val he
  rw [hv] at hc
  apply h
  change (y.1.val.card : ℤ)=(x.1.val.card : ℤ)+1
  omega

theorem zMatrix_degree (g ρ : R) (n : ℕ) :
    Verification.GradedPerturbation.Homogeneous degree 1 (zMatrix g ρ n) := by
  intro y x h
  simp only [zMatrix,matrixOf,LinearMap.toMatrix'_apply,LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [show (fun i : NormalIndex RightNormal n => if i=x then (1 : R) else 0)=Pi.single x 1 by
    funext i; simp [Pi.single_apply,eq_comm]]
  rw [zCoefficients_apply]
  rw [zDifferential_stratum_zero g ρ n _ y.1]
  · rfl
  · intro j hj
    exact zCoefficients_inverse_stratum ρ n x _ (erase_stratum_ne y x h j hj)

theorem yMatrix_degree (g ρ : R) (a : ℕ) :
    Verification.GradedPerturbation.Homogeneous degree 1 (yMatrix g ρ a) := by
  intro y x h
  simp only [yMatrix,matrixOf,LinearMap.toMatrix'_apply,LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [show (fun i : NormalIndex BothNormal (2*a) => if i=x then (1 : R) else 0)=Pi.single x 1 by
    funext i; simp [Pi.single_apply,eq_comm]]
  rw [yCoefficients_apply]
  rw [yDifferential_stratum_zero g ρ a _ y.1]
  · rfl
  · intro j hj
    exact yCoefficients_inverse_stratum ρ a x _ (erase_stratum_ne y x h j hj)

#print axioms normalCoordinates_inverse_stratum
#print axioms zCoefficients_inverse_stratum
#print axioms yCoefficients_inverse_stratum
#print axioms differential_stratum_zero
#print axioms zDifferential_stratum_zero
#print axioms yDifferential_stratum_zero
#print axioms degree
#print axioms erase_stratum_ne
#print axioms zMatrix_degree
#print axioms yMatrix_degree

end Verification.PathStratumGrading
