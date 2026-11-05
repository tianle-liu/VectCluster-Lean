/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.IntegralSmithScalarIso
import Verification.TensorFunctorIdentity
import Verification.NatComplexIntegerFree

/-!
# Finite Free Tensor Smith Homology

The ordinary full Smith kernel/cokernel formula for the actual tensor
extension of a finite free complex. The coefficient module may have torsion.
All scalar entries and ranks come from constructed boundary Smith bases.
-/
noncomputable section
namespace Verification.FiniteFreeTensorSmithHomology
open CategoryTheory
variable {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable (C : CochainComplex (ModuleCat.{0} R) ℤ)
variable [∀ n, Module.Free R (C.X n)] [∀ n, Module.Finite R (C.X n)]
variable (M : Type) [AddCommGroup M] [Module R M]

def complexIso :
    ((IntegerTensorExtension.functor R M).mapHomologicalComplex (ComplexShape.up ℤ)).obj C ≅
      ScalarBlockComplex.complex (SmithCoefficientComplex.embedding C)
        (ScalarBlockTensor.moduleEntry M (IntegralSmithScalarIso.scalar C)) :=
  (TensorFunctorIdentity.complexIso R M (ComplexShape.up ℤ) C).trans
    ((((ScalarBlockTensor.coefficientFunctor M).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
      (IntegralSmithScalarIso.scalarIso C)).trans
        (ScalarBlockTensor.tensorIso M (SmithCoefficientComplex.embedding C)
          (IntegralSmithScalarIso.scalar C)))

def homologyIso (n : ℤ) :
    (((IntegerTensorExtension.functor R M).mapHomologicalComplex (ComplexShape.up ℤ)).obj C).homology n ≅
      ModuleCat.of R (ScalarBlockComplex.HomologyTerms (SmithCoefficientComplex.embedding C)
        (ScalarBlockTensor.moduleEntry M (IntegralSmithScalarIso.scalar C)) n) :=
  ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) n).mapIso
    (complexIso C M)).trans (ScalarBlockComplex.homologyIso (SmithCoefficientComplex.embedding C)
      (ScalarBlockTensor.moduleEntry M (IntegralSmithScalarIso.scalar C)) n)

#print axioms complexIso
#print axioms homologyIso
end Verification.FiniteFreeTensorSmithHomology
