/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.UniversalExchangeChart
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Stability

/-!
# Universal Parameter Flat

The x-coordinate parameter map of the actual universal chart is flat,
proved using its polynomial localization presentation. No smooth-implies-flat
axiom or unproved local-chart identification is used.
-/
noncomputable section
universe u
namespace Verification.UniversalParameterFlat
open MvPolynomial Verification.LocalExchangeSmooth Verification.UniversalExchangeChart
variable (R κ : Type u) [CommRing R]
attribute [local instance] MvPolynomial.algebraMvPolynomial

instance polynomialParameterTower : IsScalarTower R (MvPolynomial κ R) (Polynomial R κ) :=
  IsScalarTower.of_algebraMap_eq (fun r => by
    change algebraMap R (Polynomial R κ) r =
      (SplitExchangeChart.parameterPresentation R κ).symm (C (C r))
    exact ((SplitExchangeChart.parameterPresentation R κ).symm.commutes r).symm)

def parameterEquiv : Universal R κ ≃ₐ[MvPolynomial κ R] OpenPolynomial R κ :=
  AlgEquiv.ofRingEquiv (f := (polynomialEquiv R κ).toRingEquiv) (fun p => by
    have h : (toPolynomial R κ).comp (LocalExchangeParameters.parameterMap (R := R) (targetUnit R κ)) =
        IsScalarTower.toAlgHom R (MvPolynomial κ R) (OpenPolynomial R κ) := by
      apply MvPolynomial.algHom_ext
      intro k
      change toPolynomial R κ
        (LocalExchangeParameters.parameterMap (R := R) (targetUnit R κ) (X k)) = _
      rw [LocalExchangeParameters.parameterMap, aeval_X, toPolynomial_x]
      change _ = algebraMap (MvPolynomial κ R) (OpenPolynomial R κ) (X k)
      rw [IsScalarTower.algebraMap_apply (MvPolynomial κ R) (Polynomial R κ) (OpenPolynomial R κ),
        SplitExchangeChart.parameter_algebraMap_X]
    exact AlgHom.congr_fun h p)

attribute [-instance] MvPolynomial.algebraMvPolynomial in
theorem polynomial_parameter_flat : Module.Flat (MvPolynomial κ R) (Polynomial R κ) := by
  letI : Module.Free (MvPolynomial κ R) (Polynomial R κ) :=
    Module.Free.of_equiv (SplitExchangeChart.parameterEquiv R κ).toLinearEquiv
  exact Module.Flat.of_free

theorem openPolynomial_parameter_flat : Module.Flat (MvPolynomial κ R) (OpenPolynomial R κ) := by
  letI := polynomial_parameter_flat R κ
  exact Module.Flat.trans (MvPolynomial κ R) (Polynomial R κ) (OpenPolynomial R κ)

theorem universal_parameter_flat : Module.Flat (MvPolynomial κ R) (Universal R κ) := by
  letI := openPolynomial_parameter_flat R κ
  exact Module.Flat.of_linearEquiv (parameterEquiv R κ).toLinearEquiv

#print axioms polynomialParameterTower
#print axioms parameterEquiv
#print axioms polynomial_parameter_flat
#print axioms openPolynomial_parameter_flat
#print axioms universal_parameter_flat
end Verification.UniversalParameterFlat
