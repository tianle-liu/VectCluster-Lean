/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FinitePerturbation

/-!
# Graded Perturbation

Degreewise realization of finite matrix perturbation.  Integer degrees are
attached to a finite basis.  Homogeneity is proved for the corrected contraction,
then it is used to build an actual mathlib homotopy equivalence of complexes.
-/

namespace Verification.GradedPerturbation

open CategoryTheory CategoryTheory.Category Verification.FinitePerturbation
open Finset

variable {R : Type*} [CommRing R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A matrix changes the explicit basis degree by `k`. -/
def Homogeneous (deg : ι → ℤ) (k : ℤ) (M : Matrix ι ι R) : Prop :=
  ∀ i j, deg i ≠ deg j+k → M i j = 0

omit [Fintype ι] [DecidableEq ι] in
theorem homogeneous_zero (deg : ι → ℤ) (k : ℤ) : Homogeneous deg k (0 : Matrix ι ι R) := by
  intro i j _
  rfl

omit [Fintype ι] in
theorem homogeneous_one (deg : ι → ℤ) : Homogeneous deg 0 (1 : Matrix ι ι R) := by
  intro i j hij
  have hne : i ≠ j := by intro he; subst j; simp at hij
  simp [hne]

omit [Fintype ι] [DecidableEq ι] in
theorem homogeneous_add (deg : ι → ℤ) (k : ℤ) (M N : Matrix ι ι R)
    (hM : Homogeneous deg k M) (hN : Homogeneous deg k N) : Homogeneous deg k (M+N) := by
  intro i j hij
  simp only [Matrix.add_apply, hM i j hij, hN i j hij, add_zero]

omit [Fintype ι] [DecidableEq ι] in
theorem homogeneous_sub (deg : ι → ℤ) (k : ℤ) (M N : Matrix ι ι R)
    (hM : Homogeneous deg k M) (hN : Homogeneous deg k N) : Homogeneous deg k (M-N) := by
  intro i j hij
  simp only [Matrix.sub_apply, hM i j hij, hN i j hij, sub_self]

omit [Fintype ι] [DecidableEq ι] in
theorem homogeneous_neg (deg : ι → ℤ) (k : ℤ) (M : Matrix ι ι R)
    (hM : Homogeneous deg k M) : Homogeneous deg k (-M) := by
  intro i j hij
  simp only [Matrix.neg_apply, hM i j hij, neg_zero]

omit [DecidableEq ι] in
theorem homogeneous_mul (deg : ι → ℤ) (a b : ℤ) (M N : Matrix ι ι R)
    (hM : Homogeneous deg a M) (hN : Homogeneous deg b N) : Homogeneous deg (a+b) (M*N) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply sum_eq_zero
  intro z _
  by_cases hz : deg z = deg j+b
  · rw [hM i z (by omega), zero_mul]
  · rw [hN z j hz, mul_zero]

omit [Fintype ι] [DecidableEq ι] in
theorem homogeneous_sum {J : Type*} (deg : ι → ℤ) (k : ℤ) (S : Finset J)
    (M : J → Matrix ι ι R) (hM : ∀ j ∈ S, Homogeneous deg k (M j)) :
    Homogeneous deg k (∑ j ∈ S, M j) := by
  intro i j hij
  simp only [Matrix.sum_apply]
  exact sum_eq_zero (fun z hz => hM z hz i j hij)

theorem homogeneous_pow_zero (deg : ι → ℤ) (M : Matrix ι ι R)
    (hM : Homogeneous deg 0 M) (n : ℕ) : Homogeneous deg 0 (M^n) := by
  induction n with
  | zero => simpa only [pow_zero] using homogeneous_one (R := R) deg
  | succ n ih =>
    rw [pow_succ]
    simpa only [zero_add] using homogeneous_mul deg 0 0 (M^n) M ih hM

/-- The explicit finite inverse has degree zero because every summand does. -/
theorem finiteUnit_inverse_homogeneous (deg : ι → ℤ) (N : Matrix ι ι R)
    (hN : Homogeneous deg 0 N) (n : ℕ) (hn : N^n = 0) :
    Homogeneous deg 0 (finiteUnit N n hn).inv := by
  change Homogeneous deg 0 (∑ k ∈ range n, (-N)^k)
  apply homogeneous_sum
  intro k _
  exact homogeneous_pow_zero deg (-N) (homogeneous_neg deg 0 N hN) k

/-- The simultaneous corrected contraction still lowers degree by one. -/
theorem filtered_homotopy_homogeneous (deg : ι → ℤ) (H V : Matrix ι ι R)
    (hdH : Homogeneous deg (-1) H) (hdV : Homogeneous deg 1 V)
    (w : ι → ℕ) (b : ℕ) (hw : ∀ i, w i ≤ b)
    (hH : ∀ i j, w i ≠ w j → H i j = 0)
    (hV : ∀ i j, w i ≤ w j → V i j = 0) :
    Homogeneous deg (-1) (correctedHomotopy H V (leftWeightUnit H V w b hw hH hV)) := by
  have hN : Homogeneous deg 0 (V*H) := by
    simpa using homogeneous_mul deg 1 (-1) V H hdV hdH
  have hQ : Homogeneous deg 0 (leftWeightUnit H V w b hw hH hV).inv :=
    finiteUnit_inverse_homogeneous deg (V*H) hN (b+1)
      (Verification.ChainCancellation.raising_matrix_nilpotent (V*H) w b hw
        (preserving_raising_products H V w hH hV).1)
  have hA : Homogeneous deg 1 (correction V (leftWeightUnit H V w b hw hH hV)) := by
    simpa only [zero_add] using homogeneous_mul deg 0 1 _ V hQ hdV
  have hHA : Homogeneous deg 0 (H*correction V (leftWeightUnit H V w b hw hH hV)) := by
    simpa using homogeneous_mul deg (-1) 1 H _ hdH hA
  exact homogeneous_sub deg (-1) H _ hdH
    (by simpa using homogeneous_mul deg 0 (-1) _ H hHA hdH)

/-- Actual homogeneous coordinate module, with zero coefficients in every other degree. -/
def degreeModule (deg : ι → ℤ) (p : ℤ) : Submodule R (ι → R) where
  carrier := {x | ∀ i, deg i ≠ p → x i = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy i hi; simp [hx i hi, hy i hi]
  smul_mem' := by intro a x hx i hi; simp [hx i hi]

/-- Restriction of literal matrix multiplication to its actual source and target degrees. -/
def matrixDegreeMap (deg : ι → ℤ) (M : Matrix ι ι R) (k : ℤ)
    (hM : Homogeneous deg k M) (p q : ℤ) (hpq : q = p+k) :
    degreeModule (R := R) deg p →ₗ[R] degreeModule (R := R) deg q where
  toFun x := ⟨Matrix.mulVec M x.val, by
    intro i hi
    change ∑ j, M i j*x.val j = 0
    apply sum_eq_zero
    intro j _
    by_cases hj : deg j = p
    · rw [hM i j (by omega), zero_mul]
    · rw [x.property j hj, mul_zero]⟩
  map_add' x y := by apply Subtype.ext; exact map_add (Matrix.toLin' M) _ _
  map_smul' a x := by apply Subtype.ext; exact map_smul (Matrix.toLin' M) _ _

/-- Genuine cochain complex on the finite graded basis. -/
def matrixComplex (deg : ι → ℤ) (D : Matrix ι ι R) (hD : Homogeneous deg 1 D)
    (hsq : D*D = 0) : CochainComplex (ModuleCat R) ℤ :=
  CochainComplex.of (fun p => ModuleCat.of R (degreeModule (R := R) deg p))
    (fun p => ModuleCat.ofHom (matrixDegreeMap deg D 1 hD p (p+1) rfl)) (by
      intro p
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      change Matrix.mulVec D (Matrix.mulVec D x.val) = 0
      rw [Matrix.mulVec_mulVec, hsq, Matrix.zero_mulVec])

/-- A degree-minus-one matrix, inserted in exactly the allowed homotopy positions. -/
noncomputable def homotopyFamily (deg : ι → ℤ) (D : Matrix ι ι R)
    (hD : Homogeneous deg 1 D) (hsq : D*D = 0)
    (H : Matrix ι ι R) (hH : Homogeneous deg (-1) H) :
    ∀ i j, (matrixComplex deg D hD hsq).X i ⟶ (matrixComplex deg D hD hsq).X j := by
  intro i j
  exact if hij : j+1=i then ModuleCat.ofHom (matrixDegreeMap deg H (-1) hH i j (by omega)) else 0

/-- The polynomially corrected contraction gives the required all-degree contraction data. -/
noncomputable def matrixContraction (deg : ι → ℤ) (D : Matrix ι ι R)
    (hD : Homogeneous deg 1 D) (hsq : D*D = 0)
    (H : Matrix ι ι R) (hH : Homogeneous deg (-1) H)
    (hHH : H*H = 0) (hHDH : H*D*H = H) :
    Verification.ComplexCancellation.PartialContraction (matrixComplex deg D hD hsq) where
  hom := homotopyFamily deg D hD hsq H hH
  shape i j hij := by
    have hne : ¬j+1=i := hij
    simp only [homotopyFamily, dif_neg hne]
  square i j k := by
    by_cases hij : j+1=i
    · by_cases hjk : k+1=j
      · simp only [homotopyFamily, dif_pos hij, dif_pos hjk]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        change Matrix.mulVec H (Matrix.mulVec H x.val) = 0
        rw [Matrix.mulVec_mulVec, hHH, Matrix.zero_mulVec]
      · simp only [homotopyFamily, dif_pos hij, dif_neg hjk, CategoryTheory.Limits.comp_zero]
    · simp only [homotopyFamily, dif_neg hij, CategoryTheory.Limits.zero_comp]
  regular i j := by
    by_cases hij : j+1=i
    · subst i
      simp only [homotopyFamily, dif_pos rfl, matrixComplex, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      change Matrix.mulVec H (Matrix.mulVec D (Matrix.mulVec H x.val)) = Matrix.mulVec H x.val
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hHDH]
    · simp only [homotopyFamily, dif_neg hij, CategoryTheory.Limits.zero_comp]

/-- Actual homotopy equivalence of an arbitrary finite graded complex, with no two-term truncation. -/
noncomputable def matrixCancellation (deg : ι → ℤ) (D : Matrix ι ι R)
    (hD : Homogeneous deg 1 D) (hsq : D*D = 0)
    (H : Matrix ι ι R) (hH : Homogeneous deg (-1) H)
    (hHH : H*H = 0) (hHDH : H*D*H = H) :
    HomotopyEquiv (matrixComplex deg D hD hsq)
      (Verification.ComplexCancellation.survivorComplex
        (matrixContraction deg D hD hsq H hH hHH hHDH)) :=
  Verification.ComplexCancellation.cancellation _

/-- Finite frozen-weight increase supplies the corrected contraction for the entire complex. -/
noncomputable def filteredContraction (deg : ι → ℤ) (U H V : Matrix ι ι R)
    (hdU : Homogeneous deg 1 U) (hdH : Homogeneous deg (-1) H) (hdV : Homogeneous deg 1 V)
    (hU : U*U = 0) (hHH : H*H = 0) (hHUH : H*U*H = H) (hUHU : U*H*U = U)
    (hD : (U+V)*(U+V) = 0) (w : ι → ℕ) (b : ℕ)
    (hw : ∀ i, w i ≤ b) (hH : ∀ i j, w i ≠ w j → H i j = 0)
    (hV : ∀ i j, w i ≤ w j → V i j = 0) :
    Verification.ComplexCancellation.PartialContraction
      (matrixComplex deg (U+V) (homogeneous_add deg 1 U V hdU hdV) hD) :=
  matrixContraction deg (U+V) (homogeneous_add deg 1 U V hdU hdV) hD
    (filteredCancellation U H V hU hHH hHUH hUHU hD w b hw hH hV).homotopy
    (filtered_homotopy_homogeneous deg H V hdH hdV w b hw hH hV)
    (filteredCancellation U H V hU hHH hHUH hUHU hD w b hw hH hV).homotopy_square
    (filteredCancellation U H V hU hHH hHUH hUHU hD w b hw hH hV).homotopy_regular

/-- The finite perturbation theorem as a mathlib homotopy equivalence of actual complexes. -/
noncomputable def filteredHomotopyEquiv (deg : ι → ℤ) (U H V : Matrix ι ι R)
    (hdU : Homogeneous deg 1 U) (hdH : Homogeneous deg (-1) H) (hdV : Homogeneous deg 1 V)
    (hU : U*U = 0) (hHH : H*H = 0) (hHUH : H*U*H = H) (hUHU : U*H*U = U)
    (hD : (U+V)*(U+V) = 0) (w : ι → ℕ) (b : ℕ)
    (hw : ∀ i, w i ≤ b) (hH : ∀ i j, w i ≠ w j → H i j = 0)
    (hV : ∀ i j, w i ≤ w j → V i j = 0) :
    HomotopyEquiv (matrixComplex deg (U+V) (homogeneous_add deg 1 U V hdU hdV) hD)
      (Verification.ComplexCancellation.survivorComplex
        (filteredContraction deg U H V hdU hdH hdV hU hHH hHUH hUHU hD w b hw hH hV)) :=
  Verification.ComplexCancellation.cancellation _

#print axioms Homogeneous
#print axioms homogeneous_zero
#print axioms homogeneous_one
#print axioms homogeneous_add
#print axioms homogeneous_sub
#print axioms homogeneous_neg
#print axioms homogeneous_mul
#print axioms homogeneous_sum
#print axioms homogeneous_pow_zero
#print axioms finiteUnit_inverse_homogeneous
#print axioms filtered_homotopy_homogeneous
#print axioms degreeModule
#print axioms matrixDegreeMap
#print axioms matrixComplex
#print axioms homotopyFamily
#print axioms matrixContraction
#print axioms matrixCancellation
#print axioms filteredContraction
#print axioms filteredHomotopyEquiv

end Verification.GradedPerturbation
