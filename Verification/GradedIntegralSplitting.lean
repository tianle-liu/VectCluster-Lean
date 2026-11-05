/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.IntegralSplitting
import Verification.GradedPerturbation

/-!
# Graded Integral Splitting

A contraction obtained from TF homology can be chosen with the required degree
and frozen weight.  We project a constructed generalized inverse to degree -1
and weight zero, prove UGU=U survives that projection, and normalize polynomially.
-/

namespace Verification.GradedIntegralSplitting

open Verification.GradedPerturbation Verification.FinitePerturbation

section Normalization

variable {A : Type*} [Ring A] (U G : A)

/-- Polynomial normalization of an actual generalized inverse. -/
def normalize : A := (1-U*G)*G*(U*G)

variable (hU : U*U = 0) (hUGU : U*G*U = U)

include hUGU in
theorem image_idempotent : (U*G)*(U*G) = U*G := by
  rw [← mul_assoc, hUGU]

include hU hUGU in
theorem normalize_image : U*normalize U G = U*G := by
  calc
    U*normalize U G = (U-U*(U*G))*G*(U*G) := by noncomm_ring [normalize]
    _ = (U*G)*(U*G) := by rw [square_zero_suffix U hU G, sub_zero]
    _ = U*G := image_idempotent U G hUGU

include hUGU in
theorem normalize_right : normalize U G*(U*G) = normalize U G := by
  change ((1-U*G)*G*(U*G))*(U*G) = _
  rw [mul_assoc, image_idempotent U G hUGU]
  rfl

include hUGU in
theorem normalize_left : (U*G)*normalize U G = 0 := by
  calc
    (U*G)*normalize U G = ((U*G)*(1-U*G))*G*(U*G) := by noncomm_ring [normalize]
    _ = 0 := by rw [mul_sub, mul_one, image_idempotent U G hUGU, sub_self]; simp

include hUGU in
theorem normalize_square : normalize U G*normalize U G = 0 := by
  calc
    normalize U G*normalize U G = (normalize U G*(U*G))*normalize U G := by
      rw [normalize_right U G hUGU]
    _ = normalize U G*((U*G)*normalize U G) := mul_assoc _ _ _
    _ = 0 := by rw [normalize_left U G hUGU, mul_zero]

include hU hUGU in
theorem normalize_generalized : U*normalize U G*U = U := by
  rw [normalize_image U G hU hUGU, hUGU]

include hU hUGU in
theorem normalize_regular : normalize U G*U*normalize U G = normalize U G := by
  rw [mul_assoc, normalize_image U G hU hUGU, normalize_right U G hUGU]

end Normalization

section Components

variable {R : Type*} [CommRing R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The selected degree change and weight-preserving component of a finite matrix. -/
def component (deg wt : ι → ℤ) (k : ℤ) (M : Matrix ι ι R) : Matrix ι ι R :=
  fun i j => if deg i=deg j+k ∧ wt i=wt j then M i j else 0

omit [Fintype ι] [DecidableEq ι] in
theorem component_degree (deg wt : ι → ℤ) (k : ℤ) (M : Matrix ι ι R) :
    Homogeneous deg k (component deg wt k M) := by
  intro i j hij
  simp [component, hij]

omit [Fintype ι] [DecidableEq ι] in
theorem component_weight (deg wt : ι → ℤ) (k : ℤ) (M : Matrix ι ι R) :
    Homogeneous wt 0 (component deg wt k M) := by
  intro i j hij
  simp only [add_zero] at hij
  simp [component, hij]

omit [Fintype ι] [DecidableEq ι] in
theorem off_component (deg wt : ι → ℤ) (k : ℤ) (M : Matrix ι ι R)
    (hD : Homogeneous deg k M) (hW : Homogeneous wt 0 M)
    (i j : ι) (hij : ¬(deg i=deg j+k ∧ wt i=wt j)) : M i j = 0 := by
  by_cases hd : deg i=deg j+k
  · exact hW i j (by simp only [add_zero]; intro hw; exact hij ⟨hd,hw⟩)
  · exact hD i j hd

omit [Fintype ι] [DecidableEq ι] in
theorem component_self (deg wt : ι → ℤ) (k : ℤ) (M : Matrix ι ι R)
    (hD : Homogeneous deg k M) (hW : Homogeneous wt 0 M) : component deg wt k M = M := by
  ext i j
  by_cases hij : deg i=deg j+k ∧ wt i=wt j
  · simp only [component, if_pos hij]
  · rw [component, if_neg hij, off_component deg wt k M hD hW i j hij]

omit [DecidableEq ι] in
theorem mul_component (deg wt : ι → ℤ) (a k : ℤ) (U G : Matrix ι ι R)
    (hD : Homogeneous deg a U) (hW : Homogeneous wt 0 U) :
    U*component deg wt k G = component deg wt (a+k) (U*G) := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hij : deg i=deg j+(a+k) ∧ wt i=wt j
  · rw [component, if_pos hij, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hiz : deg i=deg z+a ∧ wt i=wt z
    · have hzj : deg z=deg j+k ∧ wt z=wt j := by constructor <;> omega
      rw [component, if_pos hzj]
    · rw [off_component deg wt a U hD hW i z hiz, zero_mul, zero_mul]
  · rw [component, if_neg hij]
    apply Finset.sum_eq_zero
    intro z _
    by_cases hiz : deg i=deg z+a ∧ wt i=wt z
    · have hzj : ¬(deg z=deg j+k ∧ wt z=wt j) := by
        intro hzj
        apply hij
        constructor <;> omega
      rw [component, if_neg hzj, mul_zero]
    · rw [off_component deg wt a U hD hW i z hiz, zero_mul]

omit [DecidableEq ι] in
theorem component_mul (deg wt : ι → ℤ) (k a : ℤ) (G U : Matrix ι ι R)
    (hD : Homogeneous deg a U) (hW : Homogeneous wt 0 U) :
    component deg wt k G*U = component deg wt (k+a) (G*U) := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hij : deg i=deg j+(k+a) ∧ wt i=wt j
  · rw [component, if_pos hij, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hzj : deg z=deg j+a ∧ wt z=wt j
    · have hiz : deg i=deg z+k ∧ wt i=wt z := by constructor <;> omega
      rw [component, if_pos hiz]
    · rw [off_component deg wt a U hD hW z j hzj, mul_zero, mul_zero]
  · rw [component, if_neg hij]
    apply Finset.sum_eq_zero
    intro z _
    by_cases hzj : deg z=deg j+a ∧ wt z=wt j
    · have hiz : ¬(deg i=deg z+k ∧ wt i=wt z) := by
        intro hiz
        apply hij
        constructor <;> omega
      rw [component, if_neg hiz, zero_mul]
    · rw [off_component deg wt a U hD hW z j hzj, mul_zero]

omit [DecidableEq ι] in
/-- The selected degree-minus-one, weight-zero part still covers every pure boundary. -/
theorem component_generalized (deg wt : ι → ℤ) (U G : Matrix ι ι R)
    (hD : Homogeneous deg 1 U) (hW : Homogeneous wt 0 U) (hUGU : U*G*U=U) :
    U*component deg wt (-1) G*U = U := by
  rw [mul_component deg wt 1 (-1) U G hD hW,
    component_mul deg wt (1+(-1)) 1 (U*G) U hD hW, hUGU]
  simpa using component_self deg wt 1 U hD hW

/-- Polynomial normalization preserves the contraction's degree. -/
theorem normalize_degree (deg : ι → ℤ) (U G : Matrix ι ι R)
    (hD : Homogeneous deg 1 U) (hG : Homogeneous deg (-1) G) :
    Homogeneous deg (-1) (normalize U G) := by
  have he : Homogeneous deg 0 (U*G) := by simpa using homogeneous_mul deg 1 (-1) U G hD hG
  have hc := homogeneous_sub deg 0 1 (U*G) (homogeneous_one deg) he
  have hcg : Homogeneous deg (-1) ((1-U*G)*G) := by
    simpa using homogeneous_mul deg 0 (-1) (1-U*G) G hc hG
  simpa using homogeneous_mul deg (-1) 0 ((1-U*G)*G) (U*G) hcg he

/-- Polynomial normalization preserves the frozen weight. -/
theorem normalize_weight (wt : ι → ℤ) (U G : Matrix ι ι R)
    (hD : Homogeneous wt 0 U) (hG : Homogeneous wt 0 G) :
    Homogeneous wt 0 (normalize U G) := by
  have he : Homogeneous wt 0 (U*G) := by simpa using homogeneous_mul wt 0 0 U G hD hG
  have hc := homogeneous_sub wt 0 1 (U*G) (homogeneous_one wt) he
  have hcg : Homogeneous wt 0 ((1-U*G)*G) := by
    simpa using homogeneous_mul wt 0 0 (1-U*G) G hc hG
  simpa using homogeneous_mul wt 0 0 ((1-U*G)*G) (U*G) hcg he

end Components

section TorsionFree

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (U : Matrix ι ι R) (hU : U*U=0)
variable [NoZeroSMulDivisors R (Verification.IntegralSplitting.Homology (Matrix.toLin' U))]

omit [IsDomain R] [IsPrincipalIdealRing R]
  [NoZeroSMulDivisors R (Verification.IntegralSplitting.Homology (Matrix.toLin' U))] in
include hU in
/-- The literal matrix differential gives a square-zero linear differential. -/
theorem linear_square : (Matrix.toLin' U).comp (Matrix.toLin' U) = 0 := by
  rw [← Matrix.toLin'_mul, hU, map_zero]

/-- The ungraded integral contraction is obtained from the actual TF homology quotient. -/
noncomputable def rawContraction : Matrix ι ι R :=
  LinearMap.toMatrix' (Verification.IntegralSplitting.contraction (Matrix.toLin' U) (linear_square U hU))

/-- The constructed raw matrix is a genuine generalized inverse of the whole pure differential. -/
theorem raw_generalized : U*rawContraction U hU*U = U := by
  have he := congrArg LinearMap.toMatrix'
    (Verification.IntegralSplitting.differential_contraction_differential
      (Matrix.toLin' U) (linear_square U hU))
  simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', ← mul_assoc] using he

/-- Degree- and weight-compatible contraction, constructed solely from TF homology. -/
noncomputable def tfContraction (deg wt : ι → ℤ) : Matrix ι ι R :=
  normalize U (component deg wt (-1) (rawContraction U hU))

variable (deg wt : ι → ℤ) (hD : Homogeneous deg 1 U) (hW : Homogeneous wt 0 U)

include hD hW in
theorem tfContraction_square : tfContraction U hU deg wt*tfContraction U hU deg wt = 0 :=
  normalize_square U _ (component_generalized deg wt U _ hD hW (raw_generalized U hU))

include hD hW in
theorem tfContraction_generalized : U*tfContraction U hU deg wt*U = U :=
  normalize_generalized U _ hU (component_generalized deg wt U _ hD hW (raw_generalized U hU))

include hD hW in
theorem tfContraction_regular :
    tfContraction U hU deg wt*U*tfContraction U hU deg wt = tfContraction U hU deg wt :=
  normalize_regular U _ hU (component_generalized deg wt U _ hD hW (raw_generalized U hU))

include hD in
theorem tfContraction_degree : Homogeneous deg (-1) (tfContraction U hU deg wt) :=
  normalize_degree deg U _ hD (component_degree deg wt (-1) _)

include hW in
theorem tfContraction_weight : Homogeneous wt 0 (tfContraction U hU deg wt) :=
  normalize_weight wt U _ hW (component_weight deg wt (-1) _)

include hU hD hW in
/-- The full required contraction exists with no contraction or unit-pair splitting hypothesis. -/
theorem tf_contraction_exists : ∃ H : Matrix ι ι R,
    H*H=0 ∧ U*H*U=U ∧ H*U*H=H ∧ Homogeneous deg (-1) H ∧ Homogeneous wt 0 H := by
  exact ⟨tfContraction U hU deg wt,
    tfContraction_square U hU deg wt hD hW,
    tfContraction_generalized U hU deg wt hD hW,
    tfContraction_regular U hU deg wt hD hW,
    tfContraction_degree U hU deg wt hD,
    tfContraction_weight U hU deg wt hW⟩

include hU hD in
/-- The weight-preserving form used directly by the finite cancellation constructor. -/
theorem tf_contraction_exists_nat (w : ι → ℕ)
    (hw : ∀ i j, w i ≠ w j → U i j = 0) : ∃ H : Matrix ι ι R,
    H*H=0 ∧ U*H*U=U ∧ H*U*H=H ∧ Homogeneous deg (-1) H ∧
      ∀ i j, w i ≠ w j → H i j = 0 := by
  have hwt : Homogeneous (fun i => (w i : ℤ)) 0 U := by
    intro i j hij
    apply hw i j
    intro he
    apply hij
    simp [he]
  obtain ⟨H,hHH,hUHU,hHUH,hdeg,hweight⟩ := tf_contraction_exists U hU deg
    (fun i => (w i : ℤ)) hD hwt
  refine ⟨H,hHH,hUHU,hHUH,hdeg,?_⟩
  intro i j hij
  apply hweight i j
  simp only [add_zero]
  intro he
  exact hij (Int.ofNat_inj.mp he)

end TorsionFree

#print axioms normalize
#print axioms image_idempotent
#print axioms normalize_image
#print axioms normalize_right
#print axioms normalize_left
#print axioms normalize_square
#print axioms normalize_generalized
#print axioms normalize_regular
#print axioms component
#print axioms component_degree
#print axioms component_weight
#print axioms off_component
#print axioms component_self
#print axioms mul_component
#print axioms component_mul
#print axioms component_generalized
#print axioms normalize_degree
#print axioms normalize_weight

#print axioms linear_square
#print axioms rawContraction
#print axioms raw_generalized
#print axioms tfContraction
#print axioms tfContraction_square
#print axioms tfContraction_generalized
#print axioms tfContraction_regular
#print axioms tfContraction_degree
#print axioms tfContraction_weight
#print axioms tf_contraction_exists
#print axioms tf_contraction_exists_nat

end Verification.GradedIntegralSplitting
