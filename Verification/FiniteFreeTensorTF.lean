/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.FiniteFreeTensorSmithHomology
import Verification.SmithHomologyUnits
import Verification.ScalarUnitHomology

/-!
# Finite Free Tensor TF

The TF special case of the genuine Smith calculation. Two adjacent
integral homology groups suffice; arbitrary coefficient torsion is allowed.
-/
noncomputable section
namespace Verification.FiniteFreeTensorTF
open CategoryTheory
variable {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable (C : CochainComplex (ModuleCat.{0} R) ℤ)
variable [∀ n, Module.Free R (C.X n)] [∀ n, Module.Finite R (C.X n)]
variable (M : Type) [AddCommGroup M] [Module R M]

def homologyEquiv (n : ℤ) (hin : NoZeroSMulDivisors R (C.homology n))
    (hout : NoZeroSMulDivisors R (C.homology (n+1))) :
    (((IntegerTensorExtension.functor R M).mapHomologicalComplex (ComplexShape.up ℤ)).obj C).homology n ≃ₗ[R]
      (DiagonalHomology.Unmatched (SmithCoefficientComplex.embedding C n) → M) :=
  (FiniteFreeTensorSmithHomology.homologyIso C M n).toLinearEquiv.trans
    (ScalarUnitHomology.termsEquiv M (SmithCoefficientComplex.embedding C)
      (IntegralSmithScalarIso.scalar C) n
      (SmithHomologyUnits.scalar_isUnit C n hin) (SmithHomologyUnits.scalar_isUnit C (n+1) hout))

#print axioms homologyEquiv
end Verification.FiniteFreeTensorTF
