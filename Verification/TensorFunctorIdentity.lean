/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.IntegerTensorExtension
import Verification.ScalarBlockTensor

/-!
# Tensor Functor Identity

The explicit tensor functor used for the Witt complex is the usual
right-tensor functor used by the previously checked scalar-block calculation.
-/
noncomputable section
namespace Verification.TensorFunctorIdentity
open CategoryTheory
variable (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M]

def iso : IntegerTensorExtension.functor R M ≅ ScalarBlockTensor.coefficientFunctor M :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

def complexIso {ι : Type} (shape : ComplexShape ι)
    (C : HomologicalComplex (ModuleCat.{0} R) shape) :
    ((IntegerTensorExtension.functor R M).mapHomologicalComplex shape).obj C ≅
      ((ScalarBlockTensor.coefficientFunctor M).mapHomologicalComplex shape).obj C :=
  HomologicalComplex.Hom.isoOfComponents (fun i => (iso R M).app (C.X i))
    (by intro i j _; exact (iso R M).hom.naturality (C.d i j))

#print axioms iso
#print axioms complexIso
end Verification.TensorFunctorIdentity
