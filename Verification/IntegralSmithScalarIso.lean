/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.SmithCoefficientComplex
import Verification.ScalarBlockTensor

/-!
# Integral Smith Scalar Iso

A genuine finite free integer/PID complex is isomorphic to its
constructed scalar-pair complex before coefficient evaluation. This is
obtained from the checked Smith bases, not from assumed diagonal entries.
-/
noncomputable section
open scoped TensorProduct
namespace Verification.IntegralSmithScalarIso
open CategoryTheory
open Verification.SmithComplexCoordinates Verification.SmithScaledComplex
open Verification.SmithExtendedComplex
variable {R : Type} [CommRing R]
variable (C : CochainComplex (ModuleCat.{0} R) ℤ)

def selfExtensionIso : C ≅ scale (1 : R) (extendComplex R C) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (TensorProduct.lid R (C.X n)).symm.toModuleIso)
    (by
      intro n m _
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (1 : R) • ((1 : R) ⊗ₜ[R] (C.d n m).hom x) =
        (1 : R) ⊗ₜ[R] (C.d n m).hom x
      exact one_smul R _)

variable [IsDomain R] [IsPrincipalIdealRing R]
variable [∀ n, Module.Free R (C.X n)] [∀ n, Module.Finite R (C.X n)]

def scalar (n : ℤ) (i : Fin (boundaryRank C n)) : R := (smith C n).a i

theorem entry_eq (n : ℤ) (i : Fin (boundaryRank C n)) :
    SmithCoefficientComplex.entry C R 1 n i = ScalarBlockTensor.scalarEntry (scalar C) n i := by
  simp [SmithCoefficientComplex.entry,ScalarBlockTensor.scalarEntry,scalar]

def scalarIso : C ≅ ScalarBlockComplex.complex (SmithCoefficientComplex.embedding C)
    (ScalarBlockTensor.scalarEntry (scalar C)) :=
  ((selfExtensionIso C).trans (SmithCoefficientComplex.extendedCoefficientIso C R 1)).trans
    (eqToIso (by
      unfold SmithCoefficientComplex.coefficientComplex
      congr 1
      funext n i
      exact entry_eq C n i))

#print axioms selfExtensionIso
#print axioms scalar
#print axioms entry_eq
#print axioms scalarIso
end Verification.IntegralSmithScalarIso
