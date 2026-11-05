/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# Finite Coefficient Tensor

Literal coefficient coordinates on the tensor product of a finite free
integer module. No flatness or freeness is imposed on the coefficient module.
-/

noncomputable section
namespace Verification.FiniteCoefficientTensor
open scoped TensorProduct

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
variable (ι κ : Type*) [Fintype ι] [Fintype κ]
open scoped Classical

def finsuppEquiv : (M ⊗[ℤ] (ι →₀ ℤ)) ≃ₗ[R] (ι → M) :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl R M)
    (Finsupp.linearEquivFunOnFinite ℤ ℤ ι)).trans
      (TensorProduct.piScalarRight ℤ R M ι)

theorem finsuppEquiv_tmul (m : M) (x : ι →₀ ℤ) :
    finsuppEquiv R M ι (m ⊗ₜ[ℤ] x) = fun i => x i • m := by
  simp [finsuppEquiv]

def prodEquiv : (M ⊗[ℤ] ((ι →₀ ℤ) × (κ →₀ ℤ))) ≃ₗ[R] ((ι → M) × (κ → M)) :=
  (TensorProduct.prodRight ℤ R M (ι →₀ ℤ) (κ →₀ ℤ)).trans
    (LinearEquiv.prodCongr (finsuppEquiv R M ι) (finsuppEquiv R M κ))

theorem prodEquiv_tmul (m : M) (x : (ι →₀ ℤ) × (κ →₀ ℤ)) :
    prodEquiv R M ι κ (m ⊗ₜ[ℤ] x) = (fun i => x.1 i • m, fun i => x.2 i • m) := by
  simp [prodEquiv, finsuppEquiv_tmul]

#print axioms finsuppEquiv
#print axioms finsuppEquiv_tmul
#print axioms prodEquiv
#print axioms prodEquiv_tmul

end Verification.FiniteCoefficientTensor
