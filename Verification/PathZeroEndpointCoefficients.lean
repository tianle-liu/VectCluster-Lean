/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathEndpointWords
import Verification.PathEndpointComplex

/-!
# Path Zero Endpoint Coefficients

At rho=0 constant endpoint projectors are literal coordinate deletion,
so their surviving word coefficients are unchanged.
-/

namespace Verification.PathZeroEndpointCoefficients

open Classical Verification.PathEndpointWords Verification.PathRhoEndpoint

variable {R : Type*} [CommRing R]

theorem left_scalar_bad (w : List Bool) (hw : ¬LeftNormal w) : leftScalar (0 : R) w=0 := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons a tail =>
    cases a with
    | false => exact (hw rfl).elim
    | true => rfl

theorem right_scalar_bad (w : List Bool) (hw : ¬RightNormal w) : rightScalar (0 : R) w=0 := by
  induction w with
  | nil => exact (hw rfl).elim
  | cons a w ih =>
    cases w with
    | nil =>
      cases a with
      | false => exact (hw rfl).elim
      | true => rfl
    | cons b tail =>
      apply ih
      intro hh
      exact hw (congrArg (List.cons a) hh)

theorem left_zero_word (w : List Bool) :
    Verification.PathLeftEndpoint.projection (0 : R) (Finsupp.single w 1)=
      if LeftNormal w then Finsupp.single w 1 else 0 := by
  by_cases hw : LeftNormal w
  · rw [if_pos hw]
    exact left_projection_fixed 0 w hw
  · rw [if_neg hw,left_projection_column,left_scalar_bad w hw,zero_smul]

theorem right_zero_word (w : List Bool) :
    Verification.PathRightEndpoint.projection (0 : R) (Finsupp.single w 1)=
      if RightNormal w then Finsupp.single w 1 else 0 := by
  by_cases hw : RightNormal w
  · rw [if_pos hw]
    exact right_projection_fixed 0 w hw
  · rw [if_neg hw,right_projection_column,right_scalar_bad w hw,zero_smul]

theorem diagonal_coefficient (B : List Bool → Prop)
    (P : (List Bool →₀ R) →ₗ[R] (List Bool →₀ R))
    (hP : ∀ w, P (Finsupp.single w 1)=if B w then Finsupp.single w 1 else 0)
    (v : List Bool) (hv : B v) (x : List Bool →₀ R) : P x v=x v := by
  have he : (Finsupp.lapply v : (List Bool →₀ R) →ₗ[R] R).comp P=Finsupp.lapply v := by
    apply Finsupp.lhom_ext
    intro w r
    have hs : Finsupp.single w r=r • Finsupp.single w (1 : R) := by simp
    rw [hs,map_smul,map_smul]
    congr 1
    change P (Finsupp.single w 1) v=Finsupp.single w 1 v
    rw [hP]
    by_cases hw : B w
    · rw [if_pos hw]
    · rw [if_neg hw]
      have hne : w ≠ v := fun he => hw (he.symm ▸ hv)
      simp only [Finsupp.zero_apply,Finsupp.single_eq_of_ne hne]
  exact LinearMap.congr_fun he x

theorem left_zero_coefficient (v : List Bool) (hv : LeftNormal v) (x : List Bool →₀ R) :
    Verification.PathLeftEndpoint.projection (0 : R) x v=x v :=
  diagonal_coefficient LeftNormal _ left_zero_word v hv x

theorem right_zero_coefficient (v : List Bool) (hv : RightNormal v) (x : List Bool →₀ R) :
    Verification.PathRightEndpoint.projection (0 : R) x v=x v :=
  diagonal_coefficient RightNormal _ right_zero_word v hv x

theorem endpointConstant_zero (n : ℕ) : Verification.PathEndpointComplex.endpointConstant (0 : R) n=0 := by
  unfold Verification.PathEndpointComplex.endpointConstant
  split <;> rfl

#print axioms left_scalar_bad
#print axioms right_scalar_bad
#print axioms left_zero_word
#print axioms right_zero_word
#print axioms diagonal_coefficient
#print axioms left_zero_coefficient
#print axioms right_zero_coefficient
#print axioms endpointConstant_zero

end Verification.PathZeroEndpointCoefficients
