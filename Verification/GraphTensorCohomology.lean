/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GraphBlockComplex
import Verification.IntegerTensorExtension
import Verification.AdditiveCochainIso

/-!
# Graph Tensor Cohomology

Ordinary augmented simplicial cohomology with an arbitrary abelian
coefficient group is the homology of the integral finite free complex
extended by that group. The actual finite block splitting commutes with
this coefficient extension and with cohomology.
-/
noncomputable section
open scoped Classical
namespace Verification.GraphTensorCohomology
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] ModuleCat.isModule
variable {V C : Type} [Fintype V] [Fintype C] [LinearOrder V]
variable (G : SimpleGraph V) (c : V → C) (A : Type) [AddCommGroup A]

def simplex (SF : Finset V × Finset C) : CochainComplex (ModuleCat ℤ) ℕ :=
  IntegerTensorExtension.complex ℤ A (GraphBlockComplex.simplexComplex ℤ G c SF)

def familyHomologyIso (p : ℕ) :
    (IntegerTensorExtension.complex ℤ A (GraphBlockComplex.familyComplex ℤ G c)).homology p ≅
      ModuleCat.of ℤ ((SF : Finset V × Finset C) → (simplex G c A SF).homology p) := by
  let H := ((IntegerTensorExtension.functor ℤ A).mapHomologicalComplex (ComplexShape.up ℕ)) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) p
  letI : PreservesLimit (Discrete.functor (GraphBlockComplex.simplexComplex ℤ G c)) H :=
    preservesProduct_of_preservesBiproduct (f := GraphBlockComplex.simplexComplex ℤ G c) H
  let hlim := isLimitFanMkObjOfIsLimit H (GraphBlockComplex.simplexComplex ℤ G c)
    (GraphBlockComplex.familyProjection ℤ G c) (GraphBlockComplex.familyIsProduct ℤ G c)
  exact (hlim.conePointUniqueUpToIso (ModuleCat.productConeIsLimit
    (fun SF => (simplex G c A SF).homology p))).trans
      (AdditiveCochainIso.component (AddEquiv.refl _))

def uncompressedHomologyIso (p : ℕ) :
    (IntegerTensorExtension.complex ℤ A (GraphBlockComplex.monomialComplex ℤ G c)).homology p ≅
      ModuleCat.of ℤ ((SF : Finset V × Finset C) → (simplex G c A SF).homology p) :=
  (((IntegerTensorExtension.functor ℤ A).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) p).mapIso
      (GraphBlockComplex.monomialFamilyIso ℤ G c)).trans (familyHomologyIso G c A p)

#print axioms simplex
#print axioms familyHomologyIso
#print axioms uncompressedHomologyIso
end Verification.GraphTensorCohomology
