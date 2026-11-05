/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GradedPerturbation

/-!
# Perturbed Homology Model

The corrected matrix retraction acts on the original pure-homology summand.
This file builds that precise residual complex and its actual homotopy equivalence,
rather than leaving the target as an unspecified surviving submodule.
-/

namespace Verification.PerturbedHomologyModel

open CategoryTheory CategoryTheory.Category
open Verification.FinitePerturbation Verification.GradedPerturbation

variable {R : Type*} [CommRing R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Homogeneous vectors lying in the specified old pure-homology projection. -/
def fixedModule (deg : ι → ℤ) (P : Matrix ι ι R) (p : ℤ) : Submodule R (ι → R) where
  carrier := {x | x ∈ degreeModule (R := R) deg p ∧ P.mulVec x = x}
  zero_mem' := ⟨Submodule.zero_mem _, by simp⟩
  add_mem' hx hy := ⟨Submodule.add_mem _ hx.1 hy.1, by
    rw [Matrix.mulVec_add, hx.2, hy.2]⟩
  smul_mem' a x hx := ⟨Submodule.smul_mem _ a hx.1, by
    rw [Matrix.mulVec_smul, hx.2]⟩

/-- Restrict the computed residual boundary to the specified old pure-homology summand. -/
def fixedDifferential (deg : ι → ℤ) (P S : Matrix ι ι R)
    (hS : Homogeneous deg 1 S) (hPS : P*S = S) (p : ℤ) :
    fixedModule deg P p →ₗ[R] fixedModule deg P (p+1) where
  toFun x := ⟨S.mulVec x.val,
    (matrixDegreeMap deg S 1 hS p (p+1) rfl ⟨x.val, x.property.1⟩).property, by
      rw [Matrix.mulVec_mulVec, hPS]⟩
  map_add' x y := by apply Subtype.ext; exact map_add (Matrix.toLin' S) _ _
  map_smul' a x := by apply Subtype.ext; exact map_smul (Matrix.toLin' S) _ _

/-- The actual residual complex on the original pure-homology module. -/
def fixedComplex (deg : ι → ℤ) (P S : Matrix ι ι R)
    (hS : Homogeneous deg 1 S) (hPS : P*S = S) (hSS : S*S = 0) :
    CochainComplex (ModuleCat R) ℤ :=
  CochainComplex.of (fun p => ModuleCat.of R (fixedModule deg P p))
    (fun p => ModuleCat.ofHom (fixedDifferential deg P S hS hPS p)) (by
      intro p
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      change S.mulVec (S.mulVec x.val) = 0
      rw [Matrix.mulVec_mulVec, hSS, Matrix.zero_mulVec])

/-- The differential at any consecutive pair is the stated matrix restriction. -/
theorem matrixComplex_d (deg : ι → ℤ) (D : Matrix ι ι R)
    (hD : Homogeneous deg 1 D) (hsq : D*D = 0) (p q : ℤ) (hpq : p+1=q) :
    (matrixComplex deg D hD hsq).d p q =
      ModuleCat.ofHom (matrixDegreeMap deg D 1 hD p q hpq.symm) := by
  subst q
  exact CochainComplex.of_d _ _ _ p

/-- Degree data for an already explicitly constructed matrix retraction. -/
structure GradedRetraction (deg : ι → ℤ) (D P : Matrix ι ι R)
    extends MatrixRetraction D P where
  degreeD : Homogeneous deg 1 D
  squareD : D*D = 0
  degreeS : Homogeneous deg 1 differential
  degreeI : Homogeneous deg 0 inclusion
  degreeJ : Homogeneous deg 0 retraction
  degreeH : Homogeneous deg (-1) homotopy
  retraction_support : P*retraction = retraction
  differential_support : P*differential = differential

variable (deg : ι → ℤ) (D P : Matrix ι ι R) (T : GradedRetraction deg D P)

/-- The original actual complex. -/
def sourceComplex := matrixComplex deg D T.degreeD T.squareD

/-- The specified pure-homology target with its computed residual differential. -/
def targetComplex := fixedComplex deg P T.differential T.degreeS T.differential_support T.square

/-- Corrected inclusion, acting literally by the constructed matrix. -/
def inclusionDegree (p : ℤ) : fixedModule deg P p →ₗ[R] degreeModule (R := R) deg p where
  toFun x := matrixDegreeMap deg T.inclusion 0 T.degreeI p p (by omega) ⟨x.val,x.property.1⟩
  map_add' x y := by apply Subtype.ext; exact map_add (Matrix.toLin' T.inclusion) _ _
  map_smul' a x := by apply Subtype.ext; exact map_smul (Matrix.toLin' T.inclusion) _ _

/-- Corrected retraction lands in exactly the old pure-homology summand. -/
def retractionDegree (p : ℤ) : degreeModule (R := R) deg p →ₗ[R] fixedModule deg P p where
  toFun x := ⟨T.retraction.mulVec x.val,
    (matrixDegreeMap deg T.retraction 0 T.degreeJ p p (by omega) x).property, by
      rw [Matrix.mulVec_mulVec, T.retraction_support]⟩
  map_add' x y := by apply Subtype.ext; exact map_add (Matrix.toLin' T.retraction) _ _
  map_smul' a x := by apply Subtype.ext; exact map_smul (Matrix.toLin' T.retraction) _ _

/-- The computed inclusion is a map of the actual complexes. -/
def inclusion : targetComplex deg D P T ⟶ sourceComplex deg D P T where
  f p := ModuleCat.ofHom (inclusionDegree deg D P T p)
  comm' p q hpq := by
    have he : p+1=q := hpq
    subst q
    simp only [targetComplex, sourceComplex, fixedComplex, matrixComplex, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change D.mulVec (T.inclusion.mulVec x.val) = T.inclusion.mulVec (T.differential.mulVec x.val)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, T.inclusion_chain]

/-- The computed retraction is a map of the actual complexes. -/
def retraction : sourceComplex deg D P T ⟶ targetComplex deg D P T where
  f p := ModuleCat.ofHom (retractionDegree deg D P T p)
  comm' p q hpq := by
    have he : p+1=q := hpq
    subst q
    simp only [targetComplex, sourceComplex, fixedComplex, matrixComplex, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change T.differential.mulVec (T.retraction.mulVec x.val) = T.retraction.mulVec (D.mulVec x.val)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, T.retraction_chain]

/-- The target composite is the identity because the target is the actual `P`-fixed module. -/
theorem inclusion_retraction : inclusion deg D P T ≫ retraction deg D P T =
    𝟙 (targetComplex deg D P T) := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change T.retraction.mulVec (T.inclusion.mulVec x.val) = x.val
  rw [Matrix.mulVec_mulVec, T.retract]
  exact x.property.2

/-- The corrected homotopy witnesses the other composite on the entire complex. -/
noncomputable def retractionInclusionHomotopy :
    Homotopy (retraction deg D P T ≫ inclusion deg D P T) (𝟙 (sourceComplex deg D P T)) where
  hom i j := -homotopyFamily deg D T.degreeD T.squareD T.homotopy T.degreeH i j
  zero i j hij := by
    have hne : ¬j+1=i := hij
    simp only [homotopyFamily, dif_neg hne, neg_zero]
  comm p := by
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel p (p+1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (p-1) p by change p-1+1=p; omega)]
    have hp : p-1+1=p := by omega
    simp only [sourceComplex, homotopyFamily, dif_pos rfl, dif_pos hp, dif_pos True.intro]
    rw [matrixComplex_d deg D T.degreeD T.squareD p (p+1) rfl,
      matrixComplex_d deg D T.degreeD T.squareD (p-1) p hp]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change T.inclusion.mulVec (T.retraction.mulVec x.val) =
      -T.homotopy.mulVec (D.mulVec x.val) + D.mulVec (-T.homotopy.mulVec x.val) + x.val
    rw [Matrix.mulVec_neg]
    have he := congrArg (fun M : Matrix ι ι R => M.mulVec x.val) T.homotopy_identity
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec] at he
    rw [he]
    abel

/-- Genuine homotopy equivalence onto the original pure-homology summand. -/
noncomputable def homotopyEquiv : HomotopyEquiv (sourceComplex deg D P T) (targetComplex deg D P T) where
  hom := retraction deg D P T
  inv := inclusion deg D P T
  homotopyHomInvId := retractionInclusionHomotopy deg D P T
  homotopyInvHomId := Homotopy.ofEq (inclusion_retraction deg D P T)

/-- All grading and support properties of the finite perturbation construction are proved here. -/
def filteredRetraction (deg : ι → ℤ) (U H V : Matrix ι ι R)
    (hdU : Homogeneous deg 1 U) (hdH : Homogeneous deg (-1) H) (hdV : Homogeneous deg 1 V)
    (hU : U*U = 0) (hHH : H*H = 0) (hHUH : H*U*H = H) (hUHU : U*H*U = U)
    (hD : (U+V)*(U+V) = 0) (w : ι → ℕ) (b : ℕ)
    (hw : ∀ i, w i ≤ b) (hH : ∀ i j, w i ≠ w j → H i j = 0)
    (hV : ∀ i j, w i ≤ w j → V i j = 0) :
    GradedRetraction deg (U+V) (pureProjection U H) := by
  let q := leftWeightUnit H V w b hw hH hV
  let a := correction V q
  let p := pureProjection U H
  have hN : Homogeneous deg 0 (V*H) := by
    simpa using homogeneous_mul deg 1 (-1) V H hdV hdH
  have hQ : Homogeneous deg 0 q.inv :=
    finiteUnit_inverse_homogeneous deg (V*H) hN (b+1)
      (Verification.ChainCancellation.raising_matrix_nilpotent (V*H) w b hw
        (preserving_raising_products H V w hH hV).1)
  have hA : Homogeneous deg 1 a := by
    simpa only [zero_add] using homogeneous_mul deg 0 1 q.inv V hQ hdV
  have hUH : Homogeneous deg 0 (U*H) := by
    simpa using homogeneous_mul deg 1 (-1) U H hdU hdH
  have hHU : Homogeneous deg 0 (H*U) := by
    simpa using homogeneous_mul deg (-1) 1 H U hdH hdU
  have hP : Homogeneous deg 0 p :=
    homogeneous_sub deg 0 _ _ (homogeneous_sub deg 0 _ _ (homogeneous_one deg) hUH) hHU
  have hPA : Homogeneous deg 1 (p*a) := by
    simpa using homogeneous_mul deg 0 1 p a hP hA
  have hHA : Homogeneous deg 0 (H*a) := by
    simpa using homogeneous_mul deg (-1) 1 H a hdH hA
  have hpp : p*p = p := pureProjection_square U H hU hHH hHUH hUHU
  refine {
    toMatrixRetraction := filteredCancellation U H V hU hHH hHUH hUHU hD w b hw hH hV
    degreeD := homogeneous_add deg 1 U V hdU hdV
    squareD := hD
    degreeS := ?_
    degreeI := ?_
    degreeJ := ?_
    degreeH := filtered_homotopy_homogeneous deg H V hdH hdV w b hw hH hV
    retraction_support := ?_
    differential_support := ?_ }
  · change Homogeneous deg 1 (p*a*p)
    simpa using homogeneous_mul deg 1 0 (p*a) p hPA hP
  · change Homogeneous deg 0 (p-H*a*p)
    exact homogeneous_sub deg 0 _ _ hP
      (by simpa using homogeneous_mul deg 0 0 (H*a) p hHA hP)
  · change Homogeneous deg 0 (p-p*a*H)
    exact homogeneous_sub deg 0 _ _ hP
      (by simpa using homogeneous_mul deg 1 (-1) (p*a) H hPA hdH)
  · change p*(p-p*a*H) = p-p*a*H
    noncomm_ring [hpp, idempotent_suffix p hpp]
  · change p*(p*a*p) = p*a*p
    rw [← mul_assoc, ← mul_assoc, hpp]

/-- Simultaneous finite cancellation onto the specified old pure-homology summand.
The target differential is literally `residualDifferential`, so the integer
hyperbolic path-sum formula applies to its actual matrix. -/
noncomputable def filteredHomologyEquiv (deg : ι → ℤ) (U H V : Matrix ι ι R)
    (hdU : Homogeneous deg 1 U) (hdH : Homogeneous deg (-1) H) (hdV : Homogeneous deg 1 V)
    (hU : U*U = 0) (hHH : H*H = 0) (hHUH : H*U*H = H) (hUHU : U*H*U = U)
    (hD : (U+V)*(U+V) = 0) (w : ι → ℕ) (b : ℕ)
    (hw : ∀ i, w i ≤ b) (hH : ∀ i j, w i ≠ w j → H i j = 0)
    (hV : ∀ i j, w i ≤ w j → V i j = 0) :
    HomotopyEquiv
      (sourceComplex deg (U+V) (pureProjection U H)
        (filteredRetraction deg U H V hdU hdH hdV hU hHH hHUH hUHU hD w b hw hH hV))
      (targetComplex deg (U+V) (pureProjection U H)
        (filteredRetraction deg U H V hdU hdH hdV hU hHH hHUH hUHU hD w b hw hH hV)) :=
  homotopyEquiv _ _ _ _

#print axioms matrixComplex_d
#print axioms fixedModule
#print axioms fixedDifferential
#print axioms fixedComplex
#print axioms sourceComplex
#print axioms targetComplex
#print axioms inclusionDegree
#print axioms retractionDegree
#print axioms inclusion
#print axioms retraction
#print axioms inclusion_retraction
#print axioms retractionInclusionHomotopy
#print axioms homotopyEquiv

#print axioms filteredRetraction
#print axioms filteredHomologyEquiv

end Verification.PerturbedHomologyModel

-- Explicit dependency audit of the early module constructions.
#print axioms Verification.PerturbedHomologyModel.GradedRetraction
