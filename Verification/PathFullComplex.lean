/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PathStratumGrading

/-!
# Path Full Complex

Genuine integer-indexed chain/cochain complexes of the original finite
path strata, with constant endpoints and all rho terms retained.
-/

namespace Verification.PathFullComplex

open Classical Verification.PathEndpointWords Verification.PathNormalizedBasis
  Verification.PathEndpointCoordinates Verification.PathStratumGrading
  Verification.GradedPerturbation

variable {R : Type*} [CommRing R]

noncomputable def zCochainComplex (g ρ : R) (n : ℕ) (hg : g*g=1) (hr : (1+g)*ρ=0) :
    CochainComplex (ModuleCat R) ℤ :=
  matrixComplex degree (zMatrix g ρ n) (zMatrix_degree g ρ n) (zMatrix_squared g ρ n hg hr)

noncomputable def yCochainComplex (g ρ : R) (a : ℕ) (hg : g*g=1) (hr : (1+g)*ρ=0) :
    CochainComplex (ModuleCat R) ℤ :=
  matrixComplex degree (yMatrix g ρ a) (yMatrix_degree g ρ a) (yMatrix_squared g ρ a hg hr)

/-- Dualizing a finite graded matrix changes its degree convention explicitly. -/
theorem transpose_degree {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℤ) (D : Matrix ι ι R) (hd : Homogeneous d 1 D) :
    Homogeneous (fun i => -d i) 1 D.transpose := by
  intro y x h
  change -d y ≠ -d x+1 at h
  exact hd x y (by omega)

theorem transpose_square {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι R) (hD : D*D=0) : D.transpose*D.transpose=0 := by
  rw [← Matrix.transpose_mul,hD,Matrix.transpose_zero]

/-- Homological degree p is index -p; the matrix is the actual transpose. -/
noncomputable def zChainComplex (g ρ : R) (n : ℕ) (hg : g*g=1) (hr : (1+g)*ρ=0) :
    CochainComplex (ModuleCat R) ℤ :=
  matrixComplex (fun x => -degree x) (zMatrix g ρ n).transpose
    (transpose_degree _ _ (zMatrix_degree g ρ n))
      (transpose_square _ (zMatrix_squared g ρ n hg hr))

noncomputable def yChainComplex (g ρ : R) (a : ℕ) (hg : g*g=1) (hr : (1+g)*ρ=0) :
    CochainComplex (ModuleCat R) ℤ :=
  matrixComplex (fun x => -degree x) (yMatrix g ρ a).transpose
    (transpose_degree _ _ (yMatrix_degree g ρ a))
      (transpose_square _ (yMatrix_squared g ρ a hg hr))

#print axioms zCochainComplex
#print axioms yCochainComplex
#print axioms transpose_degree
#print axioms transpose_square
#print axioms zChainComplex
#print axioms yChainComplex

end Verification.PathFullComplex
