/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathEndpointBasis
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Path Endpoint Coordinates

Literal finite coordinate matrices of the full endpoint quotient operators.
-/

namespace Verification.PathEndpointCoordinates

open Classical Verification.PathCochains Verification.PathEndpointComplex
  Verification.PathEndpointWords Verification.PathNormalizedBasis Verification.PathEndpointBasis

variable {R : Type*} [CommRing R]

noncomputable instance normalIndexDecidableEq (B : List Bool → Prop) (n : ℕ) :
    DecidableEq (NormalIndex B n) := Classical.decEq _

/-- Evaluating the abstract finite basis is the original word coefficient. -/
theorem normalCoordinates_apply (B : List Bool → Prop) (n : ℕ)
    (x : NormalTotal (R := R) B n) (i : NormalIndex B n) :
    normalCoordinates B n x i=(x i.1).val i.2.val := rfl

noncomputable def zCoefficients (ρ : R) (n : ℕ) :
    ZModule ρ n ≃ₗ[R] (NormalIndex RightNormal n → R) :=
  (rangeEquiv RightNormal (Verification.PathRightEndpoint.projection (endpointConstant ρ n))
    (right_column_normal _) (right_projection_fixed _) n (zProjection ρ n) (fun _ _ => rfl)).trans
      (normalCoordinates RightNormal n)

noncomputable def yCoefficients (ρ : R) (a : ℕ) :
    YModule ρ a ≃ₗ[R] (NormalIndex BothNormal (2*a) → R) :=
  (rangeEquiv BothNormal ((Verification.PathLeftEndpoint.projection 0).comp
    (Verification.PathRightEndpoint.projection (endpointConstant ρ (2*a))))
      (both_column_normal _ _) (both_column_fixed _ _) (2*a) (yProjection ρ a)
        (fun _ _ => rfl)).trans (normalCoordinates BothNormal (2*a))

theorem zCoefficients_apply (ρ : R) (n : ℕ) (x : ZModule ρ n) (i : NormalIndex RightNormal n) :
    zCoefficients ρ n x i=(x.val i.1).val i.2.val := rfl

theorem yCoefficients_apply (ρ : R) (a : ℕ) (x : YModule ρ a) (i : NormalIndex BothNormal (2*a)) :
    yCoefficients ρ a x i=(x.val i.1).val i.2.val := rfl

/-- Coordinate transport used only after the actual operator has been defined. -/
noncomputable def matrixOf {M : Type*} [AddCommGroup M] [Module R M]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (E : M ≃ₗ[R] (ι → R)) (D : M →ₗ[R] M) : Matrix ι ι R :=
  LinearMap.toMatrix' (E.toLinearMap.comp (D.comp E.symm.toLinearMap))

theorem matrixOf_squared {M : Type*} [AddCommGroup M] [Module R M]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (E : M ≃ₗ[R] (ι → R)) (D : M →ₗ[R] M)
    (hd : D.comp D=0) : matrixOf E D*matrixOf E D=0 := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul,map_zero]
  simp only [matrixOf,Matrix.toLin'_toMatrix']
  apply LinearMap.ext
  intro f
  change E (D (E.symm (E (D (E.symm f)))))=0
  rw [LinearEquiv.symm_apply_apply]
  have hz := congrArg (fun T : M →ₗ[R] M => T (E.symm f)) hd
  change D (D (E.symm f))=0 at hz
  rw [hz,map_zero]

noncomputable def zMatrix (g ρ : R) (n : ℕ) :
    Matrix (NormalIndex RightNormal n) (NormalIndex RightNormal n) R :=
  matrixOf (M := ZModule ρ n) (zCoefficients ρ n) (zDifferential g ρ n)

noncomputable def yMatrix (g ρ : R) (a : ℕ) :
    Matrix (NormalIndex BothNormal (2*a)) (NormalIndex BothNormal (2*a)) R :=
  matrixOf (M := YModule ρ a) (yCoefficients ρ a) (yDifferential g ρ a)

theorem zMatrix_squared (g ρ : R) (n : ℕ) (hg : g*g=1) (hr : (1+g)*ρ=0) :
    zMatrix g ρ n*zMatrix g ρ n=0 := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul,map_zero]
  simp only [zMatrix,matrixOf,Matrix.toLin'_toMatrix']
  apply LinearMap.ext
  intro f
  change zCoefficients ρ n (zDifferential g ρ n ((zCoefficients ρ n).symm
    (zCoefficients ρ n (zDifferential g ρ n ((zCoefficients ρ n).symm f)))))=0
  rw [LinearEquiv.symm_apply_apply]
  have hz := LinearMap.congr_fun (zDifferential_squared g ρ n hg hr) ((zCoefficients ρ n).symm f)
  change zDifferential g ρ n (zDifferential g ρ n ((zCoefficients ρ n).symm f))=0 at hz
  rw [hz,map_zero]

theorem yMatrix_squared (g ρ : R) (a : ℕ) (hg : g*g=1) (hr : (1+g)*ρ=0) :
    yMatrix g ρ a*yMatrix g ρ a=0 := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul,map_zero]
  simp only [yMatrix,matrixOf,Matrix.toLin'_toMatrix']
  apply LinearMap.ext
  intro f
  change yCoefficients ρ a (yDifferential g ρ a ((yCoefficients ρ a).symm
    (yCoefficients ρ a (yDifferential g ρ a ((yCoefficients ρ a).symm f)))))=0
  rw [LinearEquiv.symm_apply_apply]
  have hz := LinearMap.congr_fun (yDifferential_squared g ρ a hg hr) ((yCoefficients ρ a).symm f)
  change yDifferential g ρ a (yDifferential g ρ a ((yCoefficients ρ a).symm f))=0 at hz
  rw [hz,map_zero]

#print axioms normalIndexDecidableEq
#print axioms normalCoordinates_apply
#print axioms zCoefficients
#print axioms yCoefficients
#print axioms zCoefficients_apply
#print axioms yCoefficients_apply
#print axioms matrixOf
#print axioms matrixOf_squared
#print axioms zMatrix
#print axioms yMatrix
#print axioms zMatrix_squared
#print axioms yMatrix_squared

end Verification.PathEndpointCoordinates
