/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.LocalExchangeTensor
import Verification.UniversalParameterFlat

/-!
# Local Parameter Flat

Flatness of the actual x-parameter map follows from the actual tensor
presentation and flatness of the character map.
-/
noncomputable section
universe u
namespace Verification.LocalParameterFlat
open MvPolynomial Verification.LocalExchangeSmooth Verification.UniversalExchangeChart
open Verification.LocalExchangeTensor
open scoped TensorProduct
variable {R S κ : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra (Target R κ) S] [IsScalarTower R (Target R κ) S]
variable (χ : κ → Sˣ)
variable (hχ : ∀ k, algebraMap (Target R κ) S (DiagonalPowerFibers.laurentCoordinate R κ k) = χ k)
attribute [local instance] MvPolynomial.algebraMvPolynomial

instance universalParameterTower : IsScalarTower R (MvPolynomial κ R) (Universal R κ) :=
  IsScalarTower.of_algHom (LocalExchangeParameters.parameterMap (R := R) (targetUnit R κ))

instance universalScalarComm : SMulCommClass (Target R κ) (MvPolynomial κ R) (Universal R κ) where
  smul_comm a b z := by
    simp only [Algebra.smul_def]
    exact mul_left_comm _ _ _

def parameterTensorEquiv : LocalAlgebra χ ≃ₐ[MvPolynomial κ R]
    BaseChange (R := R) (S := S) (κ := κ) :=
  AlgEquiv.ofRingEquiv (f := (tensorEquiv χ hχ).toRingEquiv) (fun p => by
    have h : ((toTensor χ hχ).restrictScalars R).comp (LocalExchangeParameters.parameterMap (R := R) χ) =
        IsScalarTower.toAlgHom R (MvPolynomial κ R) (BaseChange (R := R) (S := S) (κ := κ)) := by
      apply MvPolynomial.algHom_ext
      intro k
      change toTensor χ hχ (LocalExchangeParameters.parameterMap (R := R) χ (X k)) = _
      rw [LocalExchangeParameters.parameterMap, aeval_X, toTensor_x]
      change _ = algebraMap (MvPolynomial κ R) (Universal R κ) (X k) ⊗ₜ[Target R κ] (1 : S)
      rw [LocalExchangeParameters.parameter_X]
    exact AlgHom.congr_fun h p)

include hχ in
theorem parameter_flat [Module.Flat (Target R κ) S] :
    Module.Flat (MvPolynomial κ R) (LocalAlgebra χ) := by
  letI := UniversalParameterFlat.universal_parameter_flat R κ
  letI : Module.Flat (MvPolynomial κ R) (BaseChange (R := R) (S := S) (κ := κ)) :=
    Module.Flat.trans (MvPolynomial κ R) (Universal R κ) (BaseChange (R := R) (S := S) (κ := κ))
  exact Module.Flat.of_linearEquiv (parameterTensorEquiv χ hχ).toLinearEquiv

#print axioms universalParameterTower
#print axioms universalScalarComm
#print axioms parameterTensorEquiv
#print axioms parameter_flat
end Verification.LocalParameterFlat
