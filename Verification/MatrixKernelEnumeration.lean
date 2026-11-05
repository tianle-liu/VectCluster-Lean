/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.PerturbedHomologyModel

/-!
# Matrix Kernel Enumeration

Kernel coordinates do not depend on the finite enumeration or the
chosen decidable equality. This explicitly controls the instances when
transporting a genuine complex differential to finite matrix coordinates.
-/
noncomputable section
namespace Verification.MatrixKernelEnumeration
open Verification.GradedPerturbation
variable {R ι : Type*} [CommRing R] [f₁ : Fintype ι] [d₁ : DecidableEq ι]
variable (f₂ : Fintype ι) (d₂ : DecidableEq ι)
variable (deg : ι → ℤ) (D : Matrix ι ι R) (hD : Homogeneous deg 1 D)

theorem degreeMap (p q : ℤ) (h : q=p+1) :
    @matrixDegreeMap R _ ι f₁ d₁ deg D 1 hD p q h = @matrixDegreeMap R _ ι f₂ d₂ deg D 1 hD p q h := by
  cases Subsingleton.elim f₂ f₁
  cases Subsingleton.elim d₂ d₁
  rfl

def kernelEquiv (hsq : letI : Fintype ι := f₁; D*D=0) (p q : ℤ) (h : p+1=q) :
    LinearMap.ker ((@matrixComplex R _ ι f₁ d₁ deg D hD hsq).d p q).hom ≃ₗ[R]
      LinearMap.ker (@matrixDegreeMap R _ ι f₂ d₂ deg D 1 hD p q h.symm) := by
  letI : Fintype ι := f₁
  letI : DecidableEq ι := d₁
  rw [PerturbedHomologyModel.matrixComplex_d deg D hD hsq p q h]
  change LinearMap.ker (matrixDegreeMap deg D 1 hD p q h.symm) ≃ₗ[R] _
  rw [degreeMap (f₁ := f₁) (d₁ := d₁) f₂ d₂ deg D hD p q h.symm]

#print axioms degreeMap
#print axioms kernelEquiv
end Verification.MatrixKernelEnumeration
