/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.IntegerShortComplexRank
import Verification.MatrixCoefficientExtension
import Verification.TransposeReduction

/-!
# Integer Degree Matrix Rank

Degreewise rank balance for an actual homogeneous integer matrix
complex. Its adjacent blocks are literal submatrices on the degree fibers.
-/
noncomputable section
open scoped Classical
namespace Verification.IntegerDegreeMatrixRank
open CategoryTheory
open Verification.GradedPerturbation Verification.PerturbedHomologyModel
open Verification.MatrixCoefficientExtension
attribute [local instance 2000] ModuleCat.isModule
variable {ι : Type} [Fintype ι]
variable (deg : ι → ℤ) (D : Matrix ι ι ℤ)

def block (p q : ℤ) : Matrix {i // deg i=q} {i // deg i=p} ℤ :=
  D.submatrix Subtype.val Subtype.val

theorem coordinates_differential (hD : Homogeneous deg 1 D) (p q : ℤ) (hpq : q=p+1)
    (x : degreeModule (R:=ℤ) deg p) :
    degreeCoordinates deg q (matrixDegreeMap deg D 1 hD p q hpq x)=
      (block deg D p q).mulVec (degreeCoordinates deg p x) := by
  funext i
  change (∑ j,D i.val j*x.val j)=∑ j : {j // deg j=p},D i.val j.val*x.val j.val
  rw [← Fintype.sum_subtype_add_sum_subtype (fun j => deg j=p) (fun j => D i.val j*x.val j)]
  have hz : (∑ j : {j // ¬ deg j=p},D i.val j.val*x.val j.val)=0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [x.property j.val j.property,mul_zero]
  rw [hz,add_zero]

theorem block_square (hD : Homogeneous deg 1 D) (hsq : D*D=0) (p : ℤ) :
    block deg D p (p+1)*block deg D (p-1) p=0 := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul,map_zero]
  apply LinearMap.ext
  intro x
  obtain ⟨x,rfl⟩ := (degreeCoordinates (R:=ℤ) deg (p-1)).surjective x
  change (block deg D p (p+1)).mulVec
    ((block deg D (p-1) p).mulVec (degreeCoordinates deg (p-1) x))=0
  rw [← coordinates_differential deg D hD (p-1) p (by omega),
    ← coordinates_differential deg D hD p (p+1) rfl]
  have hz : matrixDegreeMap deg D 1 hD p (p+1) rfl
      (matrixDegreeMap deg D 1 hD (p-1) p (by omega) x)=0 := by
    apply Subtype.ext
    change D.mulVec (D.mulVec x.val)=0
    rw [Matrix.mulVec_mulVec,hsq,Matrix.zero_mulVec]
  rw [hz,map_zero]

def shortIso (hD : Homogeneous deg 1 D) (hsq : D*D=0) (p : ℤ) :
    (matrixComplex deg D hD hsq).sc' (p-1) p (p+1) ≅
      IntegerShortComplexRank.matrix (block deg D (p-1) p) (block deg D p (p+1))
        (block_square deg D hD hsq p) := by
  refine ShortComplex.isoMk ((degreeCoordinates deg (p-1)).toModuleIso)
    ((degreeCoordinates deg p).toModuleIso) ((degreeCoordinates deg (p+1)).toModuleIso) ?_ ?_
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (block deg D (p-1) p).mulVec (degreeCoordinates deg (p-1) x)=
      degreeCoordinates deg p ((matrixComplex deg D hD hsq).d (p-1) p x)
    rw [matrixComplex_d deg D hD hsq (p-1) p (by omega)]
    exact (coordinates_differential deg D hD (p-1) p (by omega) x).symm
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (block deg D p (p+1)).mulVec (degreeCoordinates deg p x)=
      degreeCoordinates deg (p+1) ((matrixComplex deg D hD hsq).d p (p+1) x)
    rw [matrixComplex_d deg D hD hsq p (p+1) rfl]
    exact (coordinates_differential deg D hD p (p+1) rfl x).symm

theorem balance (hD : Homogeneous deg 1 D) (hsq : D*D=0) (p : ℤ) :
    Module.finrank ℤ ((matrixComplex deg D hD hsq).homology p)+
      (block deg D (p-1) p).rank+(block deg D p (p+1)).rank=Fintype.card {i // deg i=p} := by
  let e := (matrixComplex deg D hD hsq).homologyIsoSc' (p-1) p (p+1) (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso (shortIso deg D hD hsq p)
  rw [e.toLinearEquiv.finrank_eq]
  exact IntegerShortComplexRank.matrix_balance _ _ (block_square deg D hD hsq p)

#print axioms block
#print axioms coordinates_differential
#print axioms block_square
#print axioms shortIso
#print axioms balance
end Verification.IntegerDegreeMatrixRank
