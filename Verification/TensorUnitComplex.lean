/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.IntegerTensorExtension

/-!
# Tensor Unit Complex

Tensoring the actual complex with its ground ring changes neither
its differential nor its homology.
-/
noncomputable section
open scoped TensorProduct
namespace Verification.TensorUnitComplex
open CategoryTheory
variable (R : Type) [CommRing R]

def iso {ι : Type} (shape : ComplexShape ι) (C : HomologicalComplex (ModuleCat.{0} R) shape) :
    ((IntegerTensorExtension.functor R R).mapHomologicalComplex shape).obj C ≅ C :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (TensorProduct.rid R (C.X i)).toModuleIso) (by
      intro i j _
      apply ModuleCat.hom_ext
      apply TensorProduct.ext
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro r
      change (C.d i j).hom (r • x) = r • (C.d i j).hom x
      exact map_smul _ _ _)

def homologyIso (C : CochainComplex (ModuleCat.{0} R) ℕ) (p : ℕ) :
    (IntegerTensorExtension.complex R R C).homology p ≅ C.homology p :=
  (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) p).mapIso
    (iso R (ComplexShape.up ℕ) C)

#print axioms iso
#print axioms homologyIso
end Verification.TensorUnitComplex
