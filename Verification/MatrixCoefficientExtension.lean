/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PerturbedHomologyModel
import Verification.SmithExtendedComplex
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Matrix Coefficient Extension

Tensor extension of an actual finite graded matrix complex.  The target
uses the independently defined entrywise coefficient map, and the comparison
is a chain isomorphism with an explicit coordinate formula.
-/

noncomputable section
namespace Verification.MatrixCoefficientExtension
open CategoryTheory
open scoped TensorProduct Classical
open Verification.GradedPerturbation Verification.PerturbedHomologyModel
open Verification.SmithExtendedComplex

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (deg : ι → ℤ)

def degreeCoordinates (p : ℤ) : degreeModule (R := R) deg p ≃ₗ[R] ({i // deg i=p} → R) where
  toFun x i := x.val i.val
  invFun y := ⟨fun i => if h : deg i=p then y ⟨i,h⟩ else 0, by
    intro i hi
    simp [hi]⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    by_cases hi : deg i=p
    · simp [hi]
    · simp [hi,x.property i hi]
  right_inv y := by funext i; simp [i.property]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def tensorCoordinates (p : ℤ) : (S ⊗[R] degreeModule (R := R) deg p) ≃ₗ[S]
    degreeModule (R := S) deg p :=
  ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S)
    (degreeCoordinates (R := R) deg p)).trans
      (TensorProduct.piScalarRight R S S {i // deg i=p})).trans
        (degreeCoordinates (R := S) deg p).symm

theorem tensorCoordinates_tmul (p : ℤ) (r : S) (x : degreeModule (R := R) deg p) (i : ι) :
    (tensorCoordinates deg p (r ⊗ₜ[R] x)).val i = algebraMap R S (x.val i) * r := by
  by_cases hi : deg i=p
  · simp [tensorCoordinates, degreeCoordinates, hi, Algebra.smul_def]
  · simp [tensorCoordinates, degreeCoordinates, hi,x.property i hi]

variable (D : Matrix ι ι R) (hD : Homogeneous deg 1 D) (hsq : D*D=0)

omit [Fintype ι] [DecidableEq ι] in
include hD in
theorem mapped_degree : Homogeneous deg 1 (D.map (algebraMap R S)) := by
  intro i j hij
  exact (congrArg (algebraMap R S) (hD i j hij)).trans (map_zero _)

omit [DecidableEq ι] in
include hsq in
theorem mapped_square : D.map (algebraMap R S) * D.map (algebraMap R S)=0 := by
  rw [← Matrix.map_mul,hsq]
  ext i j
  exact map_zero (algebraMap R S)

theorem differential_tmul (p : ℤ) (r : S) (x : degreeModule (R := R) deg p) :
    tensorCoordinates deg (p+1) (r ⊗ₜ[R] matrixDegreeMap deg D 1 hD p (p+1) rfl x) =
      matrixDegreeMap deg (D.map (algebraMap R S)) 1 (mapped_degree deg D hD) p (p+1) rfl
        (tensorCoordinates deg p (r ⊗ₜ[R] x)) := by
  apply Subtype.ext
  funext i
  rw [tensorCoordinates_tmul]
  change algebraMap R S (∑ j,D i j*x.val j)*r =
    ∑ j,algebraMap R S (D i j)*(tensorCoordinates deg p (r ⊗ₜ[R] x)).val j
  simp only [map_sum,map_mul,Finset.sum_mul,tensorCoordinates_tmul,mul_assoc]

/-- Actual scalar extension is the literal entrywise-mapped finite matrix complex. -/
def complexIso : extendComplex S (matrixComplex deg D hD hsq) ≅
    matrixComplex deg (D.map (algebraMap R S)) (mapped_degree deg D hD) (mapped_square D hsq) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => (tensorCoordinates deg p).toModuleIso) (by
      intro p q hpq
      have hq : p+1=q := hpq
      subst q
      change _ ≫ (matrixComplex deg (D.map (algebraMap R S))
        (mapped_degree deg D hD) (mapped_square D hsq)).d p (p+1) =
          (extensionFunctor S).map ((matrixComplex deg D hD hsq).d p (p+1)) ≫ _
      rw [matrixComplex_d deg D hD hsq p (p+1) rfl,
        matrixComplex_d deg _ (mapped_degree deg D hD) (mapped_square D hsq) p (p+1) rfl]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul r x => exact (differential_tmul deg D hD p r x).symm
      | add x y hx hy => simp only [map_add,hx,hy])

#print axioms degreeCoordinates
#print axioms tensorCoordinates
#print axioms tensorCoordinates_tmul
#print axioms mapped_degree
#print axioms mapped_square
#print axioms differential_tmul
#print axioms complexIso

end Verification.MatrixCoefficientExtension
