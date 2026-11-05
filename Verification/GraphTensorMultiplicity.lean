/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.GraphBlockMultiplicity
import Verification.GraphTensorCohomology
import Verification.GraphCohomologyTF
import Verification.ModuleAdditiveIso

/-!
# Graph Tensor Multiplicity

Each actual `(S,F)` summand is the augmented independence complex on
its available vertices. Reindexing the exact block fibers gives the
paper's product multiplicity, with arbitrary abelian coefficients.
-/
noncomputable section
open scoped Classical
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
namespace Verification.GraphTensorMultiplicity
open CategoryTheory Verification.GraphBlockMultiplicity
variable {V C : Type} [Fintype V] [Fintype C] [LinearOrder V] [LinearOrder C]
variable (G : SimpleGraph V) (c : V → C) (A : Type) [AddCommGroup A]

def labelEquiv : (Finset V × Finset C) ≃ Σ T : Finset V, Fiber c T where
  toFun SF := ⟨GraphBlocks.available c SF.1 SF.2,⟨SF,rfl⟩⟩
  invFun x := x.2.val
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨T,SF,h⟩
    cases h
    rfl

def blockEquiv (SF : Finset V × Finset C) (p : ℕ) :
    (GraphTensorCohomology.simplex G c A SF).homology p ≃+
      (GraphTensorCohomology.simplex G c A (GraphBlocks.available c SF.1 SF.2,∅)).homology p :=
  ModuleAdditiveIso.additive ((((IntegerTensorExtension.functor ℤ A).mapHomologicalComplex (ComplexShape.up ℕ)) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) p).mapIso
      (by
        have e := GraphCohomologyTF.availableComplexIso (R := ℤ) G c SF
        have he : (fun a b : C => Classical.propDecidable (a=b)) =
            (fun a b : C => LinearOrder.toDecidableEq a b) := Subsingleton.elim _ _
        rw [← he] at e
        have hv := congrArg (fun d : DecidableEq C =>
          @GraphBlocks.available V C d c SF.1 SF.2) he
        dsimp only at hv
        rw [hv] at e
        exact e))

def fiberEquiv (T : Finset V) (SF : Fiber c T) (p : ℕ) :
    (GraphTensorCohomology.simplex G c A SF.val).homology p ≃+
      (GraphTensorCohomology.simplex G c A (T,∅)).homology p := by
  rcases SF with ⟨SF,h⟩
  subst T
  exact blockEquiv G c A SF p

def familyEquiv (p : ℕ) :
    ((SF : Finset V × Finset C) → (GraphTensorCohomology.simplex G c A SF).homology p) ≃+
      ((T : Finset V) → Fin (multiplicity c T) →
        (GraphTensorCohomology.simplex G c A (T,∅)).homology p) :=
  ((LinearEquiv.piCongrLeft' ℤ
    (fun SF => (GraphTensorCohomology.simplex G c A SF).homology p)
    (labelEquiv c)).toAddEquiv.trans
      (LinearEquiv.piCurry ℤ (fun (T : Finset V) (SF : Fiber c T) =>
        (GraphTensorCohomology.simplex G c A SF.val).homology p)).toAddEquiv).trans
    ((AddEquiv.piCongrRight (fun T => AddEquiv.piCongrRight (fun SF => fiberEquiv G c A T SF p))).trans
      (AddEquiv.piCongrRight (fun T =>
        (LinearEquiv.piCongrLeft' ℤ (fun _ : Fiber c T =>
          (GraphTensorCohomology.simplex G c A (T,∅)).homology p)
            (fiberFinEquiv c T)).toAddEquiv)))

def cohomologyEquiv (p : ℕ) :
    (IntegerTensorExtension.complex ℤ A (GraphBlockComplex.monomialComplex ℤ G c)).homology p ≃+
      ((T : Finset V) → Fin (multiplicity c T) →
        (GraphTensorCohomology.simplex G c A (T,∅)).homology p) :=
  by
    have e := (ModuleAdditiveIso.additive (GraphTensorCohomology.uncompressedHomologyIso G c A p)).trans
      (familyEquiv G c A p)
    have he : (fun a b : C => Classical.propDecidable (a=b)) =
        (fun a b : C => LinearOrder.toDecidableEq a b) := Subsingleton.elim _ _
    rw [he] at e
    exact e

#print axioms labelEquiv
#print axioms blockEquiv
#print axioms fiberEquiv
#print axioms familyEquiv
#print axioms cohomologyEquiv
end Verification.GraphTensorMultiplicity
