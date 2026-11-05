/-
Copyright (c) 2026 VectCluster-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianle Liu
-/
import Verification.RecursiveResidualElimination
import Verification.BlockResidualBalance
import Verification.PathPureContractionData

/-!
# Two Degree Initial Contraction

A literal two-degree finite complex is the initial case of the same
residual elimination, using the identity projector and actual degree bases.
-/

namespace Verification.TwoDegreeInitialContraction

open Verification.GradedPerturbation Verification.PerturbedHomologyModel
  Verification.PathPureContractionData

variable {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι]

noncomputable def fixedOneEquiv (d : ι → ℤ) (p : ℤ) :
    fixedModule d (1 : Matrix ι ι R) p ≃ₗ[R] degreeModule (R := R) d p where
  toFun x := ⟨x.val,x.property.1⟩
  invFun x := ⟨x.val,x.property,Matrix.one_mulVec x.val⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def identityRetraction (d : ι → ℤ) (D : Matrix ι ι R) (hd : Homogeneous d 1 D) (hD : D*D=0) :
    GradedRetraction d D 1 where
  differential := D
  inclusion := 1
  retraction := 1
  homotopy := 0
  square := hD
  inclusion_chain := by rw [mul_one,one_mul]
  retraction_chain := by rw [mul_one,one_mul]
  retract := one_mul _
  homotopy_identity := by rw [one_mul,mul_zero,zero_mul,sub_zero,sub_zero]
  homotopy_square := mul_zero _
  homotopy_regular := by rw [zero_mul,mul_zero]
  degreeD := hd
  squareD := hD
  degreeS := hd
  degreeI := homogeneous_one d
  degreeJ := homogeneous_one d
  degreeH := homogeneous_zero d (-1)
  retraction_support := one_mul _
  differential_support := one_mul _

noncomputable def initial (d : ι → ℤ) (D : Matrix ι ι R) (hd : Homogeneous d 1 D) (hD : D*D=0)
    (hs : ∀ i,d i = -1 ∨ d i=0) {c m q : ℕ}
    (bC : Basis (Fin c) R (degreeModule (R := R) d (-1)))
    (bM : Basis (Fin m) R (degreeModule (R := R) d 0))
    (bQ : Basis (Fin q) R ((matrixComplex d D hd hD).homology 0)) (h : c+q=m) : Data d D := by
  let F := identityRetraction d D hd hD
  have hp : ∀ i j,d i ≠ -1 → d i ≠ 0 → (1 : Matrix ι ι R) i j=0 := by
    intro i j hi hi0
    exact ((hs i).elim hi hi0).elim
  let bal : (fixedModule d (1 : Matrix ι ι R) (-1) × (Fin q → R)) ≃ₗ[R]
      fixedModule d (1 : Matrix ι ι R) 0 :=
    Verification.BlockResidualBalance.basisBalance (bC.map (fixedOneEquiv d (-1)).symm)
      (bM.map (fixedOneEquiv d 0).symm) (Pi.basisFun R (Fin q)) h
  let H := Verification.RecursiveResidualElimination.contraction d D 1 F
    (homogeneous_one d) (one_mul _) hp bQ.equivFun bal
  exact {
    differential_degree := hd
    differential_square := hD
    homotopy := H
    homotopy_degree := Verification.RecursiveResidualElimination.contraction_degree d D 1 F
      (homogeneous_one d) (one_mul _) hp bQ.equivFun bal
    homotopy_square := Verification.RecursiveResidualElimination.contraction_square d D 1 F
      (homogeneous_one d) (one_mul _) (mul_one _) hp bQ.equivFun bal
    homotopy_regular := Verification.RecursiveResidualElimination.contraction_regular d D 1 F
      (homogeneous_one d) (one_mul _) (mul_one _) hp bQ.equivFun bal
    generalized := Verification.RecursiveResidualElimination.contraction_generalized d D 1 F
      (homogeneous_one d) (one_mul _) (mul_one _) hp bQ.equivFun bal
    supported := Verification.RecursiveResidualElimination.projection_supported d D 1 F
      (homogeneous_one d) (one_mul _) (mul_one _) hp bQ.equivFun bal }

#print axioms fixedOneEquiv
#print axioms identityRetraction
#print axioms initial

end Verification.TwoDegreeInitialContraction
